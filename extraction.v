Require Import "sequentialconsistency".

Extraction Language Haskell.
Extract Constant current => "()".
Extract Constant kE => "\x->x".
Extract Constant agent => "Agent".
Extract Constant knowledge "d" => "NVar d".
Extract Constant U => "()".
Extract Constant IO "a" => "IO a".

Recursive Extraction motto_comm.

