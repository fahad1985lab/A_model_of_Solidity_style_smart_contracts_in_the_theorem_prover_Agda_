open import constantparameters


module guidelines (param : ConstantParameters) where


-- This file is guidelines for the code contained in the paper.
-- The authors:  Fahad Alhabardi and Anton Setzer
-- The title of the paper: A model of the Solidity-style smart contracts in the theorem prover Agda
-- All files have been checked and worked


-- Sect I INTRODUCTION

-- Sect II RELATED WORK


-- Sect III. BACKGROUND – THE PROOF ASSISTANT AGDA AND ETHEREUM

--- Subsection A. The theorem prover Agda

open import Simple-Model.ledgerversion.Ledger-Simple-Model


--- Subsection B. Ethereum


-- Sect IV. MODELLING OF SOLIDITY SMART CONTRACTS IN AGDA

--- Subsection A. Overview on simple and complex models

--- Subsection B. Simple model of Solidity smart contracts in Agda

-- Ledger

open import Simple-Model.ledgerversion.Ledger-Simple-Model

-- An example of an increment

open import Simple-Model.example.examplecounter

--Library

open import Simple-Model.library-simple-model.basicDataStructureWithSimpleModel




--- Subsection C. Complex model of solidity smart contracts in Agda

-- Ledger

open import Complex-Model.ledgerversion.Ledger-Complex-Model

-- commands and responses

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

-- Sect V. CONCLUSION AND FUTURE WORK






























