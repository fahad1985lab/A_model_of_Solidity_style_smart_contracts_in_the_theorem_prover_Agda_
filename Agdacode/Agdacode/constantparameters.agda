{-# OPTIONS --allow-unsolved-metas #-}

module constantparameters where

open import Data.Nat
open import Data.String hiding (length)
open import Data.List
open import Data.Bool

open import basicDataStructure
open import Complex-Model.ccomand.ccommands-cresponse



record ConstantParameters : Set where
  field
    hash                   : ℕ → ℕ
    --costupdatec : this one depend on the size of the code we updated our and added ℕ to update.
                    --in response we add cost to update
    costcurrentAddrLookupc : ℕ
    costcallAddrLookupc    : ℕ
    costcallc              : Msg → ℕ
    costtransfer           : ℕ
    costgetAmount          : ℕ
    costreturn             : Msg → ℕ
    costerror              : ErrorMsg → ℕ
    costofreturn           : ℕ
    gasprice : ℕ
  GastoWei  : ℕ → ℕ  --
  GastoWei n = n * gasprice
    --NN  omit next one
    --costexec               : (c : CCommands) → (CResponse c →  ℕ)

open ConstantParameters public


exampleParameters : ConstantParameters
exampleParameters .hash  n =  1
exampleParameters .costcurrentAddrLookupc =  1
exampleParameters .costcallAddrLookupc =  1
exampleParameters .costcallc n =  1
exampleParameters .costtransfer =  1
exampleParameters .costgetAmount =  1
exampleParameters .costreturn n =  1
exampleParameters .costerror n =  1
exampleParameters .costofreturn =  1
exampleParameters .gasprice = 1
