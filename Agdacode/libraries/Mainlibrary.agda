
open import constantparameters

module libraries.Mainlibrary where

open import Data.Nat
open import Data.List hiding (_++_)
open import Agda.Builtin.Nat using (_-_; _*_)
open import Data.Unit
open import Data.Bool
open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Maybe hiding (_>>=_)
open import Data.String hiding (length;show)
open import Data.Nat.Show
open import Data.Maybe.Base as Maybe using (Maybe; nothing; _<∣>_; when)
import Data.Maybe.Effectful
open import Data.Product renaming (_,_ to _,,_ )
open import Agda.Builtin.String


--our work
open import basicDataStructure
open import libraries.natCompare
open import Complex-Model.ccomand.ccommands-cresponse



--Definition of complex smart contract
record Contract : Set where
  constructor contract
  field
    amount   : Amount
    fun  : FunctionName → Msg → SmartContractExec Msg  
    purefunction : FunctionName → Msg → MsgOrError  --this one will change because in ether the function no change only the variable can change
    purefunctionCost : FunctionName → Msg → ℕ   

open Contract public




--ledger
Ledger : Set
Ledger = Address  → Contract


-- the execution stack element
record ExecStackEl : Set where
  constructor execStackEl
  field
    lastCallAddress : Address   -- the address which made the call to the current function call
    calledAddress   : Address   -- is the address to which the last current function call was made from lastCallAddr
    continuation  : (Msg → SmartContractExec Msg) -- continuation how to proceed once a result is returned, which depends on that result which is an element of Msg
    costCont  : Msg → ℕ -- Cost for continuation depending on the msg returned when the current call is finished
-- The following two elements are only for debugging purposes so that in case of an error
    funcNameexecStackEl  : FunctionName     --functionanme is the name of the function which was called

    msgexecStackEl       : Msg --msg is the arguments with which this funciton was called.
open ExecStackEl public


-- execution stack function
ExecutionStack : Set
ExecutionStack = List ExecStackEl




-- the state execution function
record StateExecFun : Set where
  constructor stateEF
  field
    ledger : Ledger
    executionStack : ExecutionStack
    initialAddr :  Address -- the address which initiated everything
    lastCallAddr    : Address -- the address which made the call to the current function call
    calledAddr : Address   -- is the address to which the last current fucntion call was made from lastCallAddr
    nextstep  : SmartContractExec Msg   -- next step in the program to be executed when
    gasLeft   : ℕ  -- how much we have left in the next execution step

--these info regarding debug info :

    funNameevalState : FunctionName
    msgevalState : Msg
open StateExecFun public


