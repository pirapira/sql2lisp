Require Import "sequentialconsistency".

Extraction Language Ocaml.
Extract Constant current => "()".
Extract Constant kE => "\x->x".
Extract Constant agent => "AgentType".
Extract Constant knowledge "d" => "Prelude.IO d".
Extract Constant U => "()".

Recursive Extraction exchanged.

