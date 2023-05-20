open import constantparameters

module Complex-Model.example.executedvotingexample  where
open import Data.List
open import Data.Bool.Base 
open import Agda.Builtin.Unit
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Maybe hiding (_>>=_)
open import Data.Nat.Base 
open import Data.Nat.Show
open import Data.Fin.Base hiding (_+_; _-_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl ; sym ; cong)
open import Agda.Builtin.Nat using (_-_; _*_)
open import Data.String hiding (length; show) renaming (_++_ to _++str_)
open import Data.Unit
open import Data.Empty



--our work
open import  libraries.natCompare
open import Complex-Model.ledgerversion.Ledger-Complex-Model exampleParameters
open import Complex-Model.ccomand.ccommands-cresponse
open import basicDataStructure
open import libraries.IOlibrary
open import libraries.Mainlibrary
open import Complex-Model.example.votingexample




IsJust : {A : Set} → Maybe A → Set
IsJust (just _) = ⊤
IsJust nothing  = ⊥


fromJust : { A : Set} → (p : Maybe A) → IsJust p → A
fromJust (just a) tt = a




-- using function "AddVoter" with (nat 5) on testLedger

resultAfterAddVoter5 : Maybe (Ledger ×  MsgOrErrorWithGas) 
resultAfterAddVoter5 = evaluateNonTerminatingfinal testLedger 1 1 1 "addVoter" (nat 5) 20


resultReturnedAddVoter5 : MsgOrErrorWithGas
resultReturnedAddVoter5 = proj₂ (fromJust resultAfterAddVoter5 tt)
{-
evaluate to
theMsg (nat 5) , 17 gas
so executing addVoter (nat 5) returned (nat 5)
-}

ledgerAfterAdd5 : Ledger 
ledgerAfterAdd5 = proj₁ (fromJust resultAfterAddVoter5 tt)


-- check the pure function with (nat 5) after adding voter to our ledger
checkVoter5afterAdd5 : MsgOrError
checkVoter5afterAdd5 = ledgerAfterAdd5 1 .purefunction "checkVoter" (nat 5)
{-
evaluate to
theMsg (nat 1)
which means true
-}


checkVoter3AfterAdd5 : MsgOrError
checkVoter3AfterAdd5 = ledgerAfterAdd5 1 .purefunction "checkVoter" (nat 3)
{-
evaluate to
theMsg (nat 0)
which means false
-}
