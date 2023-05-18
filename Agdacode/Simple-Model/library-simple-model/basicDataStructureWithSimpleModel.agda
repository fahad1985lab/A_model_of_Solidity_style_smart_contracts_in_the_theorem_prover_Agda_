module Simple-Model.library-simple-model.basicDataStructureWithSimpleModel where

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


-- Definition of message data type
data Msg : Set where
   nat     :  (n : ℕ)         → Msg
   list    :  (l  : List Msg)  → Msg


-- Definition of error data types
data ErrorMsg : Set where
  strErr    : String → ErrorMsg


data NatOrError : Set where
 nat : ℕ → NatOrError
 err : ErrorMsg → NatOrError



