module basicDataStructure where

open import Data.Nat
open import Data.String hiding (length)
open import Data.List
open import Data.Bool
open import Agda.Builtin.String

FunctionName : Set
FunctionName = String

-- Boolean valued equality on FunctionName
_≡fun_ : FunctionName → FunctionName → Bool
_≡fun_ = primStringEquality



Time   : Set
Time   =   ℕ


Amount : Set
Amount =  ℕ


Address : Set
Address  =  ℕ


Signature : Set
Signature =  ℕ

PublicKey : Set
PublicKey  =  ℕ


data Msg : Set where
   nat     :  (n : ℕ)         → Msg
   _+msg_  :  (m m' : Msg)     → Msg
   list    :  (l  : List Msg)  → Msg



data ErrorMsg : Set where
  strErr    : String → ErrorMsg
  numErr    : ℕ → ErrorMsg
  undefined : ErrorMsg
  outOfGasError : ErrorMsg

--record (debuge) includes these info

record DebugInfo  : Set  where
       constructor ⟨_>>_∙_[_]⟩
       field
        lastcalladdr    : Address
        curraddr        : Address
        lastfunname     : FunctionName
        lastmsg         : Msg
open DebugInfo public





data NatOrError : Set where
 nat : ℕ → NatOrError
 err : ErrorMsg → DebugInfo → NatOrError
-- notNatErr : String → NatOrError
 invalidtransaction : NatOrError


--This definition we use it to display the gasleft with NatOrError
record NatOrErrorWithGas  : Set  where
       constructor _,_gas
       field
        natOrError : NatOrError
        gas    : ℕ

open NatOrErrorWithGas public




data MsgOrError : Set where
 theMsg  : Msg → MsgOrError
 err : ErrorMsg → MsgOrError



-- new definition

data MsgOrError' : Set where
 theMsg : Msg → MsgOrError'
 err : ErrorMsg → DebugInfo → MsgOrError'
--  notNatErr : String → MsgOrError'
 invalidtransaction : MsgOrError'

record MsgOrErrorWithGas  : Set  where
       constructor _,_gas
       field
        msgOrError : MsgOrError'
        gas    : ℕ
open MsgOrErrorWithGas public



-- new definition

data StringOrError' : Set where
 theString : String → StringOrError'
 err : ErrorMsg → DebugInfo → StringOrError'
 notNatErr : String → StringOrError'
 invalidtransaction : StringOrError'

record StringOrErrorWithGas  : Set  where
       constructor _,_gas
       field
        stringOrError : StringOrError'
        gas    : ℕ
open StringOrErrorWithGas public

