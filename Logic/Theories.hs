module Logic.Theories 
    ( module Logic.Theories 
    , module Logic.Theories.Arithmetic
    , module Logic.Theories.FunctionTheory
    , module Logic.Theories.IntervalTheory
    , module Logic.Theories.PredCalc
    , module Logic.Theories.RelationTheory
    , module Logic.Theories.SetTheory
    , module Logic.Theory )
where

import Logic.Expr.Classes
import Logic.Names

import Logic.Theories.Arithmetic
import Logic.Theories.FunctionTheory hiding (zrep_select)
import Logic.Theories.IntervalTheory hiding (vars)
import Logic.Theories.PredCalc       hiding (zrep_select)
import Logic.Theories.RelationTheory
import Logic.Theories.SetTheory
import Logic.Theory

import Data.Map

supportedTheories :: Map Name Theory
supportedTheories = symbol_table
    [ set_theory
    , function_theory
    , relation_theory
    , arithmetic
    , pred_calc
    , interval_theory ]

preludeTheories :: Map Name Theory
preludeTheories = symbol_table
    [ arithmetic
    , basic_theory ]
