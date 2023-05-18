open import constantparameters

module Complex-Model.example.votingexample  where
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

--our work
open import  libraries.natCompare
open import Complex-Model.ledgerversion.Ledger-Complex-Model exampleParameters
open import Complex-Model.ccomand.ccommands-cresponse
open import basicDataStructure
open import libraries.IOlibrary
open import libraries.Mainlibrary



--initial function
initialfun : Msg → MsgOrError
initialfun (nat n) = theMsg (nat 0)
initialfun owmsg   = err (strErr " The message is not a number ")


updateCounterAux2 : String → Msg → FunDef
updateCounterAux2 s (nat n) msg₁ = exec (updatec "counter" (λ x x₁ → initialfun (nat n)) λ x → 1) (λ _ → 1)
                                 λ result →  return 1 (nat (suc n )) 
updateCounterAux2 s otherwise msg₂ = return 1 (nat 17)


--increment function
-- incrementAux (theMsg (nat n)) sets the counter to n + 1
--
-- it would be clearer to define a setCounter function
--  setCounter (theMsg (nat n)) sets the counter to n
incrementAux : MsgOrError → Prog Msg
incrementAux (theMsg (nat n)) = (exec (updatec "counter" (λ _ → λ msg → theMsg (nat (suc n))) λ f → 1)
                                                         (λ n → 1)) λ x → return 1 (nat (suc n))
incrementAux ow = error (strErr "counter returns not a number") ⟨ 0 >> 0 ∙ "increment" [ (nat 0) ]⟩



--add voter function
addVoterAux : Msg → (Msg → MsgOrError) → Msg → MsgOrError
addVoterAux (nat newaddr) oldCheckVoter (nat addr) = if newaddr ≡ᵇ addr then theMsg (nat 1) else oldCheckVoter (nat addr)
addVoterAux ow ow' ow'' = err (strErr " You cannot add voter ")



--delete voter function
deleteVoterAux : Msg → (Msg → MsgOrError) → (Msg → MsgOrError)
deleteVoterAux (nat newaddr) oldCheckVoter (nat addr) = if newaddr ≡ᵇ addr then theMsg (nat 0) else oldCheckVoter (nat addr)
deleteVoterAux ow ow' ow'' = err (strErr " You cannot delete voter ")



-- the function below we use it in case to check voter is allowed to vote or not 
voteAux : MsgOrError → Prog Msg
{- first case: the voter is NOT allowed to vote -}
voteAux (theMsg (nat zero)) = error (strErr "The message is zero") ⟨ 0 >> 0 ∙ " Voter is not allowed to vote " [ nat 0 ]⟩
{- first case: the voter is allowed to vote -}
voteAux (theMsg (nat (suc n))) = (exec (callPure 5 "counter" (nat 0)) (λ result → 1))
                                  λ msg → incrementAux msg
  {- values before  need to be revised, you need to add more arguments to voteAux0  -}
voteAux (theMsg ow) = error (strErr " The message is not a number ") ⟨ 0 >> 0 ∙ " Voter is not allowed to vote " [ nat 0 ]⟩
  {- values before  need to be revised, you need to add more arguments to voteAux0  -}
voteAux (err x) = error (strErr " Undefined ") ⟨ 0 >> 0 ∙ " The message is undefined " [ nat 0 ]⟩






testLedger : Ledger
testLedger 1 .amount = 100                                                                                        

-- in case to add voter
testLedger 1 .fun "addVoter" msg  = exec (updatec "checkVoter"
                                    (addVoterAux msg) λ _ → 1)(λ _ → 1)
                                    λ _ → return 1 msg                                           
-- in case to delete voter
testLedger 1 .fun "deleteVoter" msg = exec (updatec "checkVoter" (deleteVoterAux msg) λ _ → 1)
                                      (λ _ → 1) λ _ → return 1 msg
-- in case to vote
testLedger 1 .fun "vote" msg = exec callAddrLookupc  (λ _ → 1)
                               λ addr → exec (callPure addr "checkVoter" (nat addr))
                               (λ _ → 1) λ check → voteAux check
-- in case to check voter
testLedger 1 .purefunction "checkVoter" msg = theMsg (nat 0)

-- for other cases
testLedger ow .amount = 0
testLedger ow .fun ow' ow'' = error (strErr "Undefined") ⟨ ow >> ow ∙ ow' [ ow'' ]⟩
testLedger ow .purefunction ow' ow'' = err (strErr "Undefined")


