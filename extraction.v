Require Import "sequentialconsistency".

Extraction Language Haskell.
Extract Constant current => "()".
Extract Constant kE => "\x->x".
Extract Constant agent => "Agent".
Extract Constant knowledge "'data" => "'data".
Extract Constant U => "()".

Recursive Extraction motto_comm.

