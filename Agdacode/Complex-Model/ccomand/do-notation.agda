open import constantparameters


module Complex-Model.ccomand.do-notation (param : ConstantParameters) where

open import Data.Nat
open import Agda.Builtin.Nat using (_-_)
open import Data.Unit
open import Data.List
open import Data.Bool
open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Maybe  hiding (_>>=_)
open import Data.String hiding (length)


--our work
open import basicDataStructure
open import libraries.natCompare
open import Complex-Model.ccomand.ccommands-cresponse


--- theses functions below we use them with do notation
--functionofreturn : CResponse (callc addr fname msg) → ℕ

call : (addr : Address)  → FunctionName → (Msg → ℕ) → (Msg → SmartContractExec Msg)
call addr fname cost msg  = exec (callc addr fname msg) (costcallc param) λ r → return (cost r) r  

update : FunctionName → (Msg → SmartContractExec Msg) → (cost₁  cost₂ : ℕ ) → SmartContractExec ⊤
update fname fdef cost₁ cost₂ = exec (updatec fname (λ _ fdef → theMsg fdef) λ _ → cost₁) (λ _ → cost₁) (return cost₂) 

currentAddrLookup : (cost : Address → ℕ) → SmartContractExec Address
currentAddrLookup cost = exec currentAddrLookupc (λ _ → costcurrentAddrLookupc param) λ addr → return (cost addr) addr

callAddrLookup : (cost : Address → ℕ) → SmartContractExec Address
callAddrLookup cost = exec callAddrLookupc (λ _ → costcallAddrLookupc param) λ addr → return (cost addr) addr 

transfer : Amount → Address → (cost : ℕ) → SmartContractExec ⊤
transfer amount addr cost =  exec (transferc amount addr) (λ _ → costtransfer param) (return cost) 
