
module Simple-Model.example.examplecounter where

open import Data.Nat
open import Data.List
open import Data.Bool
open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Maybe hiding (_>>=_)
open import Data.String hiding (length)


--simple model
open import Simple-Model.ledgerversion.Ledger-Simple-Model

--library
open import Simple-Model.library-simple-model.basicDataStructureWithSimpleModel




--Example of a simple counter
const : ℕ → (Msg → SmartContractExec Msg)
const n msg = return (nat n)


mutual

  contract0 : FunctionName → (Msg → SmartContractExec Msg)
  contract0 "f1" = const 0
  contract0 "g1" = def-g1
  contract0 ow ow' = error (strErr " Error msg") 
  


  def-g1 : (Msg → SmartContractExec Msg)
  def-g1 msg = do
                 addr       ← currentAddrLookup
                 (nat n)    ← call 0 "f1" (nat 0)
                  where
                  (list l)    → error (strErr " Error msg") 
                 update "f1" (const (suc n))
                 return (nat n)


-- test our ledger with our example

testLedger : Ledger

testLedger 0 .amount  = 20
testLedger 0 .fun "f1" m = const 0 (nat 0)
testLedger 0 .fun "g1" m = def-g1(nat 0)
testLedger 0 .fun "k1" m =
             exec (getAmountc 0) (λ n → return (nat n))
testLedger 0 .fun  ow ow' =
             error (strErr "Undefined")

-- the example belw we use it in our paper

testLedger 1 .amount = 40
testLedger 1 .fun "f1" m = const 0 (nat 0)
testLedger 1 .fun "g1" m = 
  exec currentAddrLookupc  λ addr →
  exec (callc addr "f1" (nat 0))
  λ{(nat n)  → exec (updatec "f1" (const (suc n)))
                λ _ → return (nat (suc n));
    _        → error (strErr
               "f1 returns not a number")}
testLedger 1 .fun  ow' ow''  =
           error (strErr "Undefined")


--otherwise
testLedger ow .amount = 0
testLedger ow .fun ow' ow'' = error (strErr "Undefined")



-- test cases below

-- test the ledger above
test : NatOrError
test = evaluateNonTerminating testLedger 0 0 "f1" (nat 0) 
--return nat 0

updatefunctionf1 : NatOrError
updatefunctionf1 = evaluateNonTerminating testLedger 0 1 "g1" (nat 0)
--return nat 1
