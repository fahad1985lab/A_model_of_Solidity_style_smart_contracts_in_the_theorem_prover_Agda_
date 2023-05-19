module libraries.emptyLib  where

open import Data.Empty


empty : {A : Set} → ⊥ → A
empty ()
