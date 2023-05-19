open import constantparameters


module loadAll (param : ConstantParameters) where


-- This file is guidelines for the code contained in the paper.
-- The authors:  Fahad Alhabardi and Anton Setzer
-- The title of the paper: A model of the Solidity-style smart contracts in the theorem prover Agda


                ----------------------
                -- Root Directory   --
                ----------------------

open import basicDataStructure
open import constantparameters



                ----------------------------
                --   libraries directory  --
                ----------------------------
open import libraries.Mainlibrary
open import libraries.IOlibrary
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

-- do notation

open import Complex-Model.ccomand.do-notation


-- comands and response

open import Complex-Model.ccomand.ccommands-cresponse


-- A voting example

open import Complex-Model.example.votingexample


-- Executed voting example

open import Complex-Model.example.executedvotingexample



























