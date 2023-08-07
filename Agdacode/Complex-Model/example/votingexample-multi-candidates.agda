open import constantparameters

module Complex-Model.example.votingexample-multi-candidates  where
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
open import libraries.Mainlibrary



--initial function
initialfun : Msg → MsgOrError
initialfun (nat n) = theMsg (nat 0)
initialfun owmsg   = err (strErr " The message is not a number ")



mysuc : MsgOrError → MsgOrError
mysuc (theMsg (nat n)) = theMsg (nat (suc n))
mysuc (theMsg  ow)= err (strErr " You cannot increment ")
mysuc ow = ow


-- incrementAux for many candidates
--increment function
incrementcandidates : ℕ → (Msg → MsgOrError) → Msg → MsgOrError
incrementcandidates candidateVotedFor oldCounter (nat candidate) = if candidateVotedFor ≡ᵇ candidate then mysuc (oldCounter (nat candidate)) else oldCounter (nat candidate)
incrementcandidates ow ow' ow'' = err (strErr " You cannot delete voter ")

incrementAux : MsgOrError → SmartContractExec Msg
incrementAux (theMsg (nat candidate)) = (exec (updatec "counter" (incrementcandidates candidate) λ oldFun oldcost msg → 1)
                                                          (λ n → 1)) λ x → return 1 (nat candidate)
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
-- in case nat 0 or otherwise it will return error and not allow to vote
-- in case suc (nat n) it will allow to vote and it will call incrementAux to increment the counter
voteAux :  Address → MsgOrError → (candidate : Msg) → SmartContractExec Msg
voteAux addr (theMsg (nat zero)) candidate
                          = error (strErr "The voter is not allowed to vote")
                            ⟨ 0 >> 0 ∙ "Voter is not allowed to vote" [ nat 0 ]⟩
voteAux addr (theMsg (nat (suc n))) candidate
                          = exec (updatec "checkVoter" (deleteVoterAux (nat addr)) λ oldFun oldcost msg → 1) (λ _ → 1)
                            (λ x → (incrementAux (theMsg candidate)))
voteAux addr (theMsg ow) candidate
                          = error (strErr "The message is not a number")
                            ⟨ 0 >> 0 ∙ "Voter is not allowed to vote" [ nat 0 ]⟩
voteAux addr (err x) candidate
                          = error (strErr " Undefined ")
                            ⟨ 0 >> 0 ∙ "The message is undefined" [ nat 0 ]⟩




-----define our ledger

testLedger : Ledger
testLedger 1 .amount = 100                                                                                        

-- in case to add voter
testLedger 1 .fun "addVoter" msg  = exec (updatec "checkVoter" (addVoterAux msg) λ oldFun oldcost msg → 1)(λ _ → 1)
                                    λ _ → return 1 msg                                           
-- in case to delete voter
testLedger 1 .fun "deleteVoter" msg = exec (updatec "checkVoter" (deleteVoterAux msg) λ oldFun oldcost msg → 1)
                                      (λ _ → 1) λ _ → return 1 msg
-- in case to vote
testLedger 1 .fun "vote" msg = exec callAddrLookupc  (λ _ → 1)
                               λ addr → exec (callPure addr "checkVoter" (nat addr))
                               (λ _ → 1) λ check → voteAux addr check msg
-- in case to check voter
testLedger 1 .purefunction "checkVoter" msg = theMsg (nat 0)

-- in case to increment our counter
testLedger 1 .purefunction "counter" msg = theMsg (nat 0)
testLedger 1 .purefunctionCost "checkVoter" msg = 1
-- define a ledger for address 3 with amount only
testLedger 3 .amount = 100

-- for other cases
testLedger ow .amount = 0
testLedger ow .fun ow' ow'' = error (strErr "Undefined") ⟨ ow >> ow ∙ ow' [ ow'' ]⟩
testLedger ow .purefunction ow' ow'' = err (strErr "Undefined")
testLedger ow .purefunctionCost ow' ow'' = 1

