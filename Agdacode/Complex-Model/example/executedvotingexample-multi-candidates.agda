open import constantparameters

module Complex-Model.example.executedvotingexample-multi-candidates  where
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
open import libraries.Mainlibrary
open import Complex-Model.example.votingexample-multi-candidates


IsJust : {A : Set} → Maybe A → Set
IsJust (just _) = ⊤
IsJust nothing  = ⊥


fromJust : {A : Set} → (p : Maybe A) → IsJust p → A
fromJust (just a) tt = a

--------------------------- First test   (adding voter)
-- using function "AddVoter" with (nat 1) on testLedger

resultAfterAddVoter1 : Ledger ×  MsgOrErrorWithGas
resultAfterAddVoter1 = evaluateTerminatingfinal testLedger 1 1 1 "addVoter" (nat 1) 20


resultReturnedAddVoter1 : MsgOrErrorWithGas
resultReturnedAddVoter1 = proj₂ resultAfterAddVoter1
{-
evaluate to
theMsg (nat 1) , 16 gas
so executing addVoter (nat 1) returned (nat 1)
-}

ledgerAfterAdd1 : Ledger
ledgerAfterAdd1 = proj₁ resultAfterAddVoter1


-- check the pure function with (nat 1) after adding voter to our ledger
checkVoter1afterAdd1 : MsgOrError
checkVoter1afterAdd1 = ledgerAfterAdd1 1 .purefunction "checkVoter" (nat 1)
{-
evaluate to
theMsg (nat 1)
which means true
-}


checkVoter3AfterAdd1 : MsgOrError
checkVoter3AfterAdd1 = ledgerAfterAdd1 1 .purefunction "checkVoter" (nat 3)
{-
evaluate to
theMsg (nat 0)
which means false
our ledger only includes (nat 1)
-}



----------------------------- Second test   (vote)
-- using function "vote" with (nat 4) on ledgerAfterAdd5

resultAfterVote : Ledger ×  MsgOrErrorWithGas
resultAfterVote = evaluateTerminatingfinal ledgerAfterAdd1 1 1 1 "vote" (nat 4) 50

resultReturnedVote : MsgOrErrorWithGas
resultReturnedVote = proj₂ resultAfterVote

{- evaluates to

theMsg (nat 4) , 39 gas

-}


ledgerAfterVote : Ledger
ledgerAfterVote = proj₁ resultAfterVote

-- check the pure function "counter" with (nat 4) after adding voter to our ledger
checkCounterAfterVote : MsgOrError
checkCounterAfterVote = ledgerAfterVote 1 .purefunction "counter" (nat 4)
-- evaluates to
-- theMsg (nat 1) which means our counter has one 


-- check the pure function "counter" with (nat 3) after adding voter to our ledger
checkCounterWith3 : MsgOrError
checkCounterWith3 = ledgerAfterVote 1 .purefunction "counter" (nat 3)
-- evaluates to
-- theMsg (nat 0) which means we do not have (nat 3) in our counter





--------------------------- Third test   (adding voter)
-- using function "AddVoter" with (nat 1) on ledgerAfterVote

resultAfterAddVoter1' : Ledger ×  MsgOrErrorWithGas
resultAfterAddVoter1' = evaluateTerminatingfinal ledgerAfterVote 1 1 1 "addVoter" (nat 1) 20


resultReturnedAddVoter1' : MsgOrErrorWithGas
resultReturnedAddVoter1' = proj₂ resultAfterAddVoter1'
{-
evaluate to
theMsg (nat 1) , 16 gas
so executing addVoter (nat 1) returned (nat 1)
-}

ledgerAfterAdd1' : Ledger
ledgerAfterAdd1' = proj₁ resultAfterAddVoter1'


-- check the pure function with (nat 1) after adding voter to our ledger
checkVoter1afterAdd1' : MsgOrError
checkVoter1afterAdd1' = ledgerAfterAdd1' 1 .purefunction "checkVoter" (nat 1)
{-
evaluate to
theMsg (nat 1)
which means true
-}


checkVoter3AfterAdd1' : MsgOrError
checkVoter3AfterAdd1' = ledgerAfterAdd1' 1 .purefunction "checkVoter" (nat 3)
{-
evaluate to
theMsg (nat 0)
which means false
our ledger only includes (nat 1)
-}



----------------------------- Fourth test   (vote)
-- using function "vote" with (nat 4) on ledgerAfterAdd5

resultAfterVote' : Ledger ×  MsgOrErrorWithGas
resultAfterVote' = evaluateTerminatingfinal ledgerAfterAdd1' 1 1 1 "vote" (nat 4) 50

resultReturnedVote' : MsgOrErrorWithGas
resultReturnedVote' = proj₂ resultAfterVote'

{- evaluates to

theMsg (nat 4) , 39 gas

-}


ledgerAfterVote' : Ledger
ledgerAfterVote' = proj₁ resultAfterVote'

-- check the pure function "counter" with (nat 4) after adding voter to our ledger
checkCounterAfterVote' : MsgOrError
checkCounterAfterVote' = ledgerAfterVote' 1 .purefunction "counter" (nat 4)
-- evaluates to
-- theMsg (nat 2) which means our counter have 2 

-- check the pure function "counter" with (nat 3) after adding voter to our ledger
checkCounterWith3' : MsgOrError
checkCounterWith3' = ledgerAfterVote' 1 .purefunction "counter" (nat 3)
-- evaluates to
-- theMsg (nat 0) which means we do not have (nat 3) in our counter





--------------------------- Fifith test   (adding voter)
-- using function "AddVoter" with (nat 1) on ledgerAfterAdd1'

resultAfterAddVoter1'' : Ledger ×  MsgOrErrorWithGas
resultAfterAddVoter1'' = evaluateTerminatingfinal ledgerAfterVote' 1 1 1 "addVoter" (nat 1) 20


resultReturnedAddVoter1'' : MsgOrErrorWithGas
resultReturnedAddVoter1'' = proj₂ resultAfterAddVoter1'
{-
evaluate to
theMsg (nat 1) , 16 gas
so executing addVoter (nat 1) returned (nat 1)
-}

ledgerAfterAdd1'' : Ledger
ledgerAfterAdd1'' = proj₁ resultAfterAddVoter1''


-- check the pure function with (nat 1) after adding voter to our ledger
checkVoter1AfterAdd1'' : MsgOrError
checkVoter1AfterAdd1'' = ledgerAfterAdd1'' 1 .purefunction "checkVoter" (nat 1)
{-
evaluate to
theMsg (nat 1)
which means true
-}


checkVoter3AfterAdd1'' : MsgOrError
checkVoter3AfterAdd1'' = ledgerAfterAdd1'' 1 .purefunction "checkVoter" (nat 3)
{-
evaluate to
theMsg (nat 0)
which means false
our ledger only includes (nat 1)
-}





----------------------------- Sixth test   (vote)
-- using function "vote" with (nat 4) on ledgerAfterAdd5

resultAfterVote'' : Ledger ×  MsgOrErrorWithGas
resultAfterVote'' = evaluateTerminatingfinal ledgerAfterAdd1'' 1 1 1 "vote" (nat 4) 50

resultReturnedVote'' : MsgOrErrorWithGas
resultReturnedVote'' = proj₂ resultAfterVote''

{- evaluates to

theMsg (nat 4) , 39 gas

-}


ledgerAfterVote'' : Ledger
ledgerAfterVote'' = proj₁ resultAfterVote''

-- check the pure function "counter" with (nat 4) after adding voter to our ledger
checkCounterAfterVote'' : MsgOrError
checkCounterAfterVote'' = ledgerAfterVote'' 1 .purefunction "counter" (nat 4)
-- evaluates to
-- theMsg (nat 3) which means our counter have 3 

-- check the pure function "counter" with (nat 3) after adding voter to our ledger
checkCounterWith3'' : MsgOrError
checkCounterWith3'' = ledgerAfterVote'' 1 .purefunction "counter" (nat 3)
-- evaluates to
-- theMsg (nat 0) which means we do not have (nat 3) in our counter
