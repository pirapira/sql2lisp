(* Avron et al. Encoding Modal Logics in Logical Frameworks *)

Parameter agent : Set.

Require Import List.

Parameter U : Type.

Parameter o: Type.

(* Model Properties *)
Parameter judgement : U -> o -> Prop.

(* Syntax *)
Parameter embed : Prop -> o.
Parameter knowledge : agent -> o -> o.
Parameter vee: o->o->o.
Parameter wedge: o->o->o.
Parameter supset: o->o->o.
Parameter ff: o.

Axiom valid: forall P: Prop, forall u: U,
  P -> judgement u (embed P).

Axiom kE: forall phi: o, forall u: U, forall a: agent,
  judgement u (knowledge a phi) -> judgement u phi.

(* a bit cumbersome. fix it to list style *)
Axiom kI: forall phi: o, forall psi: o, forall u: U, forall a: agent,
  judgement u (knowledge a psi) ->
  (forall v: U, (judgement v psi -> judgement v phi)) ->
  judgement u (knowledge a phi).

Axiom veeIl: forall phi:o, forall psi:o, forall u:U,
  judgement u phi -> judgement u (vee phi psi).

Axiom veeIr: forall phi:o, forall psi:o, forall u:U,
  judgement u psi -> judgement u (vee psi phi).

Axiom veeE: forall phi:o, forall psi:o, forall theta:o, forall u: U,
  judgement u (vee phi psi) ->
  (judgement u phi -> judgement u theta) ->
  (judgement u psi -> judgement u theta) ->
  judgement u theta.

Axiom wedgeI: forall phi:o, forall psi:o, forall u: U,
  judgement u phi ->
  judgement u psi ->
  judgement u (wedge phi psi).

Axiom wedgeEl: forall phi:o, forall psi:o, forall u:U,
  judgement u (wedge phi psi) ->
  judgement u phi.

Axiom wedgeEr: forall phi:o, forall psi:o, forall u:U,
  judgement u (wedge phi psi) ->
  judgement u psi.

Axiom supsetI: forall phi:o, forall psi:o, forall u:U,
  (judgement u phi -> judgement u psi) -> judgement u (supset phi psi).

Axiom supsetE: forall phi:o, forall psi:o, forall u:U,
  judgement u (supset phi psi) ->
  judgement u phi ->
  judgement u psi.

Axiom Kvee: forall phi:o, forall psi:o, forall theta:o, forall u:U, forall a:agent,
  judgement u (knowledge a (vee phi psi)) ->
  (judgement u (knowledge a phi) -> judgement u theta) ->
  (judgement u (knowledge a psi) -> judgement u theta) ->
  judgement u theta.


Lemma everywhere00: forall u:U, judgement u (embed (0 = 0)).
intro u.
apply valid.
reflexivity.
Qed.

Parameter shmem : agent.


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


