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

(* Model Property *)
Axiom valid: forall P: Prop, forall u: U,
  P -> judgement u (embed P).
Axiom back:
  forall P: Prop,
  (forall u:U, judgement u (embed P)) -> P.
Axiom mp:
  forall P Q: Prop,
    (P -> Q) -> (forall u: U, judgement u (embed P) -> judgement u (embed Q)).

(* Proof Rules *)
Axiom kE: forall phi: o, forall u: U, forall a: agent,
  judgement u (knowledge a phi) -> judgement u phi.

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
apply False_ind.
apply ques.
intro v.
intro everywhere.
apply valid.
reflexivity.
Qed.

Print everywherek00.
Print False_ind.

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
  apply False_ind.
  apply ab.
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

Lemma supset_meta:  
  forall P Q: Prop,
    (P->Q) -> (forall u:U, judgement u (supset (embed P) (embed Q))).
  intros P Q.
  intro meta.
  intro u.
  apply supsetI.
  intro pre.
  apply mp with P.
  exact meta.
  exact pre.
  Qed.


Lemma disj_distr:
  forall L M:Prop,
    (forall (u:U),
      (judgement u (vee (embed L) (embed M)) ->
        (judgement u (embed (L\/M))))).
  intros L M u.
  intro sem.
  apply veeE with (embed L) (embed M).
  exact sem.
  apply mp.
  intro l.
  left.
  exact l.
  apply mp.
  intro r.
  right.
  exact r.
  Qed.

Lemma disj_meta:
 forall L M:Prop, (forall (u:U), (judgement u (vee (embed L) (embed M)))) -> L\/M.
intro L.
intro M.
intro formal.
apply back.
intro u.
apply veeE with (embed L) (embed M).
apply formal.
apply mp.
intro.
left.
exact H.
apply mp.
intro.
right.
exact H.
Qed.
  
Section sequential_consistency.
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
    (judgement u (knowledge th0 phi)) ->
    (judgement u (knowledge th1 psi)) ->
    (judgement u (vee (knowledge th0 psi) (knowledge th1 phi))).
  intros phi psi u.
  intros init0 init1.
  apply veeE with 
    (supset
      (knowledge th0 (knowledge shmem (knowledge th0 phi)))
      (knowledge th0 (knowledge shmem (knowledge th1 psi))))
    (supset
      (knowledge th1 (knowledge shmem (knowledge th1 psi)))
      (knowledge th1 (knowledge shmem (knowledge th0 psi)))).
  apply veeE with
    (knowledge th1 (knowledge th0
      (supset
        (knowledge shmem (knowledge th0 phi))
        (knowledge shmem (knowledge th1 psi)))))
    (knowledge th1 (knowledge th0
      (supset
        (knowledge shmem (knowledge th1 psi))
        (knowledge shmem (knowledge th0 phi))))).
  apply Kvee with 
    (knowledge th0 (supset (knowledge shmem (knowledge th0 phi))
      (knowledge shmem (knowledge th1 psi))))
    (knowledge th0 (supset (knowledge shmem (knowledge th1 psi))
      (knowledge shmem (knowledge th0 phi))))
    th1.
  apply kI with nil.
  intro psi0.
  intro abs.
  apply False_ind.
  apply abs.
  intro v.
  intro psi0.
  apply Kvee with
    (supset (knowledge shmem (knowledge th0 phi))
              (knowledge shmem (knowledge th1 psi)))
    (supset (knowledge shmem (knowledge th1 psi))
              (knowledge shmem (knowledge th0 phi)))
    th0.
  apply kI with nil.
  intro psi1.
  intro pre.
  apply False_ind.
  apply pre.
  intro v0.
  intro psi1.
  apply sequential_consistency.
  intro lef.
  apply veeIl.
  exact lef.
  intro rig.
  apply veeIr.
  exact rig.
  intro pre.
  apply veeIl.
  exact pre.
  intro pre.
  apply veeIr.
  exact pre.
  intro pre.
  apply veeIl.
  apply supsetI.
  intro th0mem0.
  apply kI with 
    (cons (knowledge shmem (knowledge th0 phi))
      (cons
        (supset
          (knowledge shmem (knowledge th0 phi))
          (knowledge shmem (knowledge th1 psi)))
        nil)).
  intro phi0.
  intro contain.
  induction contain.
  rewrite <- H.
  exact th0mem0.
  induction H.
  rewrite <- H.
  apply kE with th1.
  exact pre.
  apply False_ind.
  apply H.
  intro v.
  intro psi0.
  apply supsetE with (knowledge shmem (knowledge th0 phi)).
  apply kE with th0.
  apply psi0.
  apply in_cons.
  apply in_eq.
  apply kE with th0.
  apply psi0.
  apply in_eq.
  intro rit.
  apply veeIr.
  apply supsetI.
  intro pre.
  apply kI with
    (knowledge shmem (knowledge th1 psi) ::
      (supset (knowledge shmem (knowledge th1 psi))
                   (knowledge shmem (knowledge th0 phi))) ::
      nil).
  intro psi0.
  intro contain.
  induction contain.
  rewrite <- H.
  exact pre.
  induction H.
  rewrite <- H.
  apply kI with
    ((knowledge th0
                (supset (knowledge shmem (knowledge th1 psi))
                   (knowledge shmem (knowledge th0 phi)))) :: nil).
  intro psi1.
  intro contain.
  induction contain.
  rewrite <- H0.
  exact rit.
  apply False_ind.
  apply H0.
  intro v.
  intro psi1.
  apply kE with th0.
  apply kE with th1.
  apply psi1.
  apply in_eq.
  apply False_ind.
  apply H.
  intro v.
  intro psi0.
