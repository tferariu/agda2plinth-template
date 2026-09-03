module Validators.AccountSim where

import Lib (Address, AssetClass, PubKeyHash, TokenName, TxOutRef)
import Value (Value, assetClassValue, emptyValue, geq, minValue)

type Label = [(PubKeyHash, Value)]

type Datum = (AssetClass, Label)

data Redeemer = Open PubKeyHash
              | Close PubKeyHash
              | Withdraw PubKeyHash Value
              | Deposit PubKeyHash Value
              | Transfer PubKeyHash PubKeyHash Value
              | Stop

insert :: PubKeyHash -> Value -> Label -> Label
insert pkh val [] = [(pkh, val)]
insert pkh val ((x, y) : xs)
  = if pkh == x then (pkh, val) : xs else (x, y) : insert pkh val xs

delete :: PubKeyHash -> Label -> Label
delete pkh [] = []
delete pkh ((x, y) : xs)
  = if pkh == x then xs else (x, y) : delete pkh xs

lookup :: PubKeyHash -> Label -> Maybe Value
lookup pkh [] = Nothing
lookup pkh ((x, y) : xs)
  = if pkh == x then Just y else lookup pkh xs

type Params = ()

checkEmpty :: Maybe Value -> Bool
checkEmpty Nothing = False
checkEmpty (Just v) = v == emptyValue

checkWithdraw ::
              AssetClass ->
                Maybe Value ->
                  PubKeyHash -> Value -> Label -> ScriptContext -> Bool
checkWithdraw tok Nothing _ _ _ _ = False
checkWithdraw tok (Just v) pkh val map ctx
  = geq val emptyValue &&
      geq v val && newDatum ctx == (tok, insert pkh (v - val) map)

checkDeposit ::
             AssetClass ->
               Maybe Value ->
                 PubKeyHash -> Value -> Label -> ScriptContext -> Bool
checkDeposit tok Nothing _ _ _ _ = False
checkDeposit tok (Just v) pkh val map ctx
  = geq val emptyValue &&
      newDatum ctx == (tok, insert pkh (v + val) map)

checkTransfer ::
              AssetClass ->
                Maybe Value ->
                  Maybe Value ->
                    PubKeyHash -> PubKeyHash -> Value -> Label -> ScriptContext -> Bool
checkTransfer tok Nothing _ _ _ _ _ _ = False
checkTransfer tok (Just vF) Nothing _ _ _ _ _ = False
checkTransfer tok (Just vF) (Just vT) from to val map ctx
  = geq val emptyValue &&
      geq vF val &&
        from /= to &&
          newDatum ctx ==
            (tok, insert from (vF - val) (insert to (vT + val) map))

agdaValidator ::
              Params -> Datum -> Redeemer -> ScriptContext -> Bool
agdaValidator par (tok, map) red ctx
  = checkTokenIn tok ctx &&
      case red of
          Open pkh -> checkTokenOut tok ctx &&
                        continuing ctx &&
                          checkSigned pkh ctx &&
                            isNothing (lookup pkh map) &&
                              newDatum ctx == (tok, insert pkh emptyValue map) &&
                                newValue ctx == oldValue ctx
          Close pkh -> checkTokenOut tok ctx &&
                         continuing ctx &&
                           checkSigned pkh ctx &&
                             checkEmpty (lookup pkh map) &&
                               newDatum ctx == (tok, delete pkh map) &&
                                 newValue ctx == oldValue ctx
          Deposit pkh val -> checkTokenOut tok ctx &&
                               continuing ctx &&
                                 checkSigned pkh ctx &&
                                   checkDeposit tok (lookup pkh map) pkh val map ctx &&
                                     newValue ctx == oldValue ctx + val
          Withdraw pkh val -> checkTokenOut tok ctx &&
                                continuing ctx &&
                                  checkSigned pkh ctx &&
                                    checkWithdraw tok (lookup pkh map) pkh val map ctx &&
                                      newValue ctx == oldValue ctx - val
          Transfer from to val -> checkTokenOut tok ctx &&
                                    continuing ctx &&
                                      checkSigned from ctx &&
                                        checkTransfer tok (lookup from map) (lookup to map) from to
                                          val
                                          map
                                          ctx
                                          && newValue ctx == oldValue ctx
          Stop -> checkTokenBurned tok ctx &&
                    not (continuing ctx) && map == []

checkDatum :: Address -> TokenName -> ScriptContext -> Bool
checkDatum addr tn ctx
  = case newDatumAddr addr ctx of
        (tok, map) -> ownAssetClass tn ctx == tok && map == []

checkValue :: Address -> TokenName -> ScriptContext -> Bool
checkValue addr tn ctx
  = checkTokenOutAddr addr (ownAssetClass tn ctx) ctx &&
      newValueAddr addr ctx ==
        minValue + assetClassValue (ownAssetClass tn ctx) 1

agdaPolicy ::
           Params ->
             Address -> TxOutRef -> TokenName -> () -> ScriptContext -> Bool
agdaPolicy par addr oref tn _ ctx
  = if amt == 1 then
      continuingAddr addr ctx &&
        consumes oref ctx &&
          checkDatum addr tn ctx && checkValue addr tn ctx
      else if amt == (-1) then not (continuingAddr addr ctx) else False
  where
    amt :: Integer
    amt = getMintedAmount ctx

