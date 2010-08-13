Require Import "sequentialconsistency".

Extraction Language Haskell.
Extract Constant current => "()".
Extract Constant kE => "\x->x".
Extract Constant agent => "AgentType".
Extract Constant knowledge "d" => "NVar d".
Extract Constant U => "()".
Extract Constant io "a" => "Prelude.IO a".

Recursive Extraction motto_comm.

