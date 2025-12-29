# agda2plinth-template
Prototype verification methodology, wherein Plutus contracts are modeled and
formally verified in Agda. These contracts are then compiled to Plinth via
the agda2hs transpiler. This includes three example smart contract validators,
as well as the token minting policy necessary to ensure their initial state.
There is also a template to be used when applying the same process to other
smart contracts.

# Versions

- agda2hs-base: v1.4 (uses Agda v2.8.0 as a library)
- agda-stdlib: v2.3

# Setup instructions

- To just typecheck the Agda files:
```
$ agda index.agda
```
- To compile the Agda files to Haskell (under the Validators/ directory):
```
$ agda2hs index.agda --config=rewriteConfig.yaml
```
