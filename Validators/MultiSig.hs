module Validators.MultiSig where

import Lib (Address, AssetClass, POSIXTime, PubKeyHash, TokenName, TxOutRef, before)
import Numeric.Natural (Natural)
import Value (Value, geq, lovelaces, minValue, x2MinValue)

data Label = Holding
           | Collecting Value PubKeyHash Integer [PubKeyHash]

type Datum = (AssetClass, Label)

data Redeemer = Propose Value PubKeyHash Integer
              | Add PubKeyHash
              | Pay
              | Cancel
              | Stop

data Params = Params{authSigs :: [PubKeyHash], minSigs :: Natural,
                     maxWait :: Integer}

insert :: PubKeyHash -> [PubKeyHash] -> [PubKeyHash]
insert pkh [] = [pkh]
insert pkh (x : l')
  = if pkh == x then x : l' else x : insert pkh l'

expired :: Integer -> ScriptContext -> Bool
expired d ctx = before (POSIXTime d) (validRange ctx)

notTooLate :: Params -> Integer -> ScriptContext -> Bool
notTooLate par d ctx
  = before (POSIXTime (d - maxWait par)) (validRange ctx)

agdaValidator ::
              Params -> Datum -> Redeemer -> ScriptContext -> Bool
agdaValidator param (tok, lab) red ctx
  = checkTokenIn tok ctx &&
      case (lab, red) of
          (Holding, Propose v pkh d) -> newValue ctx == oldValue ctx &&
                                          geq (oldValue ctx) (v + minValue) &&
                                            geq v minValue &&
                                              notTooLate param d ctx &&
                                                continuing ctx &&
                                                  checkTokenOut tok ctx &&
                                                    case newDatum ctx of
                                                        (tok', Holding) -> False
                                                        (tok', Collecting v' pkh' d' sigs') -> v ==
                                                                                                 v'
                                                                                                 &&
                                                                                                 pkh
                                                                                                   ==
                                                                                                   pkh'
                                                                                                   &&
                                                                                                   d ==
                                                                                                     d'
                                                                                                     &&
                                                                                                     sigs'
                                                                                                       ==
                                                                                                       []
                                                                                                       &&
                                                                                                       tok
                                                                                                         ==
                                                                                                         tok'
          (Collecting v pkh d sigs, Add sig) -> newValue ctx == oldValue ctx
                                                  &&
                                                  checkSigned sig ctx &&
                                                    elem sig (authSigs param) &&
                                                      continuing ctx &&
                                                        checkTokenOut tok ctx &&
                                                          case newDatum ctx of
                                                              (tok', Holding) -> False
                                                              (tok',
                                                               Collecting v' pkh' d' sigs') -> v ==
                                                                                                 v'
                                                                                                 &&
                                                                                                 pkh
                                                                                                   ==
                                                                                                   pkh'
                                                                                                   &&
                                                                                                   d ==
                                                                                                     d'
                                                                                                     &&
                                                                                                     sigs'
                                                                                                       ==
                                                                                                       insert
                                                                                                         sig
                                                                                                         sigs
                                                                                                       &&
                                                                                                       tok
                                                                                                         ==
                                                                                                         tok'
          (Collecting v pkh d sigs, Pay) -> lengthNat sigs >= minSigs param
                                              &&
                                              continuing ctx &&
                                                checkTokenOut tok ctx &&
                                                  case newDatum ctx of
                                                      (tok', Holding) -> checkPayment pkh v ctx &&
                                                                           newValue ctx + v ==
                                                                             oldValue ctx
                                                                             && tok == tok'
                                                      (tok', Collecting v' pkh' d' sigs') -> False
          (Collecting v pkh d sigs, Cancel) -> newValue ctx == oldValue ctx
                                                 &&
                                                 continuing ctx &&
                                                   checkTokenOut tok ctx &&
                                                     case newDatum ctx of
                                                         (tok', Holding) -> expired d ctx &&
                                                                              tok == tok'
                                                         (tok',
                                                          Collecting v' pkh' d' sigs') -> False
          (Holding, Stop) -> lovelaces x2MinValue > lovelaces (oldValue ctx)
                               && not (continuing ctx) && checkTokenBurned tok ctx
          _ -> False

checkDatum :: Address -> TokenName -> ScriptContext -> Bool
checkDatum addr tn ctx
  = case newDatumAddr addr ctx of
        (tok, Holding) -> ownAssetClass tn ctx == tok
        (tok, Collecting _ _ _ _) -> False

checkValue :: Address -> TokenName -> ScriptContext -> Bool
checkValue addr tn ctx
  = geq (newValueAddr addr ctx) x2MinValue &&
      checkTokenOutAddr addr (ownAssetClass tn ctx) ctx

noDups :: [PubKeyHash] -> Bool
noDups [] = True
noDups (x : xs) = not (elem x xs) && noDups xs

checkParams :: Params -> Bool
checkParams par
  = noDups (authSigs par) &&
      lengthNat (authSigs par) >= minSigs par && maxWait par > 0

agdaPolicy ::
           Params ->
             Address -> TxOutRef -> TokenName -> () -> ScriptContext -> Bool
agdaPolicy par addr oref tn _ ctx
  = if amt == 1 then
      continuingAddr addr ctx &&
        consumes oref ctx &&
          checkDatum addr tn ctx && checkValue addr tn ctx && checkParams par
      else if amt == (-1) then not (continuingAddr addr ctx) else False
  where
    amt :: Integer
    amt = getMintedAmount ctx

