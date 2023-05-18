module Complex-Model.ccomand.ccommands-cresponse where

open import Data.Nat
open import Agda.Builtin.Nat using (_-_)
open import Data.Unit
open import Data.List
open import Data.Bool
open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Maybe  hiding (_>>=_)
open import Data.String hiding (length)
open import Data.Empty


-- libraries
open import basicDataStructure
open import libraries.natCompare



mutual

  -- contract-comands:
  data CCommands : Set where
    updatec : FunctionName → ((Msg → MsgOrError) → (Msg → MsgOrError))
            → ((Msg → MsgOrError) → ℕ) → CCommands
    currentAddrLookupc : CCommands
    callAddrLookupc : CCommands
    callc   : Address → FunctionName → Msg → CCommands
    callPure : Address → FunctionName → Msg → CCommands   --callStatic into callPure 
    transferc : Amount → Address →  CCommands
    getAmountc : Address → CCommands
    raiseException : ℕ → String → CCommands --==> we used error instead of it
    

  CResponse : CCommands → Set
  CResponse (updatec fname fdef cost) = ⊤
  CResponse currentAddrLookupc = Address
  CResponse callAddrLookupc = Address
  CResponse (getAmountc addr) = Amount
  CResponse (callc addr fname msg) = Msg
  CResponse (transferc amount addr) = ⊤
  CResponse (raiseException _ str) = ⊥
  CResponse (callPure addr fname msg) = MsgOrError --callStatic into callPure




--Prog is datatype of what happens when a function is applied to its arguments.
--Prog --> Prog
  data Prog (A : Set) : Set where
    return : ℕ → A → Prog A
    error  : ErrorMsg →  DebugInfo → Prog A
    exec  : (c : CCommands) → (CResponse c →  ℕ) → (CResponse c → Prog A) → Prog A



  FunDef : Set
  FunDef = Msg → Prog Msg --Prog Msg



_>>=_ : {A B : Set} → Prog A → (A → Prog B) → Prog B
return n x >>= q    = q x
error x z >>= q     = error x z
exec c n x >>= q  = exec c n (λ r → x r >>= q)


_>>_ : {A B : Set} → Prog A → Prog B → Prog B
return n x >> q   = q
error x z >> q    = error x z
exec c n x >> q = exec c n (λ r → x r >> q)

