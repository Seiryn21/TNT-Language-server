{-# LANGUAGE OverloadedStrings #-}

module TLS.Errors where

import Data.Text

axiomRangeError :: Text 
axiomRangeError = "Axiom number must be between 1 and 5 inclusive"

theoremMeBeDeclaredAboveError :: Text
theoremMeBeDeclaredAboveError = "Theorem must be declared above to avoid cyclic reference"

theoremUnprovenWarning :: Text 
theoremUnprovenWarning = "Theorem not proven"