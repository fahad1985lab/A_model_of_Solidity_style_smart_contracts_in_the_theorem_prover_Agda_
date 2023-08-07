open import constantparameters


module loadAll (param : ConstantParameters) where


-- This file is loadAll for Agda code.
-- The authors:  Fahad Alhabardi and Anton Setzer
-- The title of the paper: A model of the Solidity-style smart contracts in the theorem prover Agda
-- All files have been checked and worked


                ----------------------
                -- Root Directory   --
                ----------------------

open import basicDataStructure
open import constantparameters



                ----------------------------
                --   libraries directory  --
                ----------------------------
open import libraries.Mainlibrary
open import libraries.emptyLib
open import libraries.natCompare




                -------------------------------
                --   Simple Model directory  --
                -------------------------------

-- Ledger

open import Simple-Model.ledgerversion.Ledger-Simple-Model

-- A count example

open import Simple-Model.example.examplecounter


-- library for simple model

open import Simple-Model.library-simple-model.basicDataStructureWithSimpleModel




               -------------------------------
               --   Complex Model directory --
               -------------------------------

-- Ledger

open import Complex-Model.ledgerversion.Ledger-Complex-Model

-- comands and response

open import Complex-Model.ccomand.ccommands-cresponse


-- A voting example for single candidate

open import Complex-Model.example.votingexample-single-candidate

-- Executed voting example for single candidate

open import Complex-Model.example.executedvotingexample-single-candidate



-- a more democratic one with multiple candidates

-- A voting example for multiple candidates

open import Complex-Model.example.votingexample-multi-candidates

-- Executed voting example for multiple candidates

open import Complex-Model.example.executedvotingexample-multi-candidates




























