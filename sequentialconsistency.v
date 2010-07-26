Parameter agent : Set.

Parameter knowledge : agent -> Prop -> Prop.

Axiom T: forall L:Prop, forall a:agent, knowledge a L -> L.

Axiom A4: forall L:Prop, forall a:agent, knowledge a L -> knowledge a (knowledge a L).

Axiom KV: forall L :Prop, forall M:Prop, forall a:agent, knowledge a (L \/ M) ->
  knowledge a L \/ knowledge a M.

(* KI needed. *)

Parameter shmem : agent.

Axiom sequential_consistency:
  forall L:Prop, forall M:Prop,
    (knowledge shmem L -> knowledge shmem M) \/ (knowledge shmem M -> knowledge shmem L).

Parameter threads: Set.

Axiom writeNVar:
  forall L:Prop, forall a:agent,
    knowledge a L -> knowledge a (knowledge shmem (knowledge a L)).

Lemma exchange:
  forall L:Prop, forall M:Prop, (forall a:agent, forall b:agent,
    knowledge a L -> knowledge b M -> knowledge a M \/ knowledge b L).
intro L.
intro M.
intro a.
intro b.
intro ka.
intro kb.
apply writeNVar in ka.
apply writeNVar in kb.


