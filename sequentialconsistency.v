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
Axiom back:
  forall P: Prop,
  (forall u:U, judgement u (embed P)) -> P.

Axiom kE: forall phi: o, forall u: U, forall a: agent,
  judgement u (knowledge a phi) -> judgement u phi.

(* a bit cumbersome. fix it to list style *)
Axiom kI: forall phi: o, forall ps: list o, forall u: U, forall a: agent,
  (forall psi: o, In psi ps -> judgement u (knowledge a psi)) ->
  (forall v: U, ((forall psi: o, In psi ps -> judgement v (knowledge a psi))
    -> judgement v phi)) ->
  judgement u (knowledge a phi).

Axiom veeIl: forall phi:o, forall psi:o, forall u:U,
  judgement u phi -> judgement u (vee phi psi).

Axiom veeIr: forall phi:o, forall psi:o, forall u:U,
  judgement u psi -> judgement u (vee phi psi).

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

Lemma everywherek00: forall u:U, forall a:agent,
  judgement u (knowledge a (embed (0 = 0))).
intro u.
intro a.
apply kI with nil.
intro psi.
intro ques.
absurd (In psi nil).
auto.
auto.
intro v.
intro everywhere.
apply valid.
reflexivity.
Qed.

Lemma skk: forall (u:U) (phi:o),
  judgement u (supset phi phi).
  intro u.
  intro phi.
  apply supsetI.
  auto.
  Qed.

Lemma knows_skk:  forall (u:U) (phi:o) (a:agent),
  judgement u (knowledge a (supset phi phi)).
  intro u.
  intro phi.
  intro a.
  apply kI with nil.
  intro psi.
  intro ab.
  absurd (In psi nil).
  auto.
  auto.
  intro v.
  intro psi.
  apply skk.
  Qed.

Lemma kv: forall (u:U) (phi psi:o) (a:agent),
  judgement u (supset
    (knowledge a (vee phi psi))
    (vee (knowledge a phi) (knowledge a psi))).
  intro u.
  intro phi.
  intro psi.
  intro a.
  apply supsetI.
  intro kor.
  apply Kvee with phi psi a.
  exact kor.
  intro lefty.
  apply veeIl.
  exact lefty.
  intro righty.
  apply veeIr.
  exact righty.
  Qed.
  

Lemma disj_meta:
  forall (u:U) (phi psi:o),
  (judgement u (vee phi psi)) -> (judgement u phi) \/ judgement u psi.
intro u.
intro phi.
intro psi.
intro formal.

  
Section consistency.
Parameter shmem th0 th1: agent.
Axiom write0:
  forall (psi: o) (u: U),
  judgement u (knowledge th0 psi) ->
  judgement u (knowledge th0 (knowledge shmem (knowledge th0 psi))).
Axiom write1:
  forall (psi: o) (u: U),
    judgement u (knowledge th1 psi) ->
    judgement u (knowledge th0 (knowledge shmem (knowledge th0 psi))).
Axiom sequential_consistency:
  forall (phi psi: o) (u: U),
    judgement u
    (vee (supset (knowledge shmem phi) (knowledge shmem psi))
      (supset (knowledge shmem psi) (knowledge shmem phi))).

Lemma comm:
  forall (phi psi: o) (u: U),
    judgement u (knowledge th0 phi) ->
    judgement u (knowledge th1 psi) ->
    (judgement u (knowledge th0 psi)) 
      
    


