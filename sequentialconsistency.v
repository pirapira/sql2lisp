(* Avron et al. Encoding Modal Logics in Logical Frameworks *)

Parameter agent : Set.

Require Import List.

Parameter U : Type.
Parameter current: U.

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

Definition validity (phi : o) : Prop :=
  forall u:U, judgement u phi.

(* Model Property *)
Axiom valid: forall P: Prop,
  P -> validity (embed P).
Axiom back: forall P: Prop,
  judgement current (embed P) -> P.


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


Lemma disj_current_embed: forall (L M: Prop),
  judgement current (vee (embed L) (embed M)) ->
  L \/ M.
  intros L M.
  intro pre.
  apply back.
  apply veeE with (embed L) (embed M).
  exact pre.
  apply mp.
  left.
  exact H.
  apply mp.
  right.
  exact H.
  Qed.

Lemma disj_current: forall (phi psi: o),
  judgement current (vee phi psi) ->
  judgement current phi \/ judgement current psi.
  intros phi psi.
  intro pre.
  apply back.
  apply veeE with phi psi.
  exact pre.
  intro two.
  apply valid.
  left.
  exact two.
  intro two.
  apply valid.
  right.
  exact two.
  Qed.


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
 forall L M:Prop, (validity (vee (embed L) (embed M))) -> L\/M.
intro L.
intro M.
intro formal.
apply back.
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

Lemma simplerKvee:
  forall (u: U) (phi psi: o) (a:agent),
    (judgement u (knowledge a (vee phi psi))) ->
    (judgement u (vee (knowledge a phi)
      (knowledge a psi))).
  intros u phi psi a.
  intro pre.
  apply Kvee with phi psi a.
  exact pre.
  apply veeIl.
  apply veeIr.
  Qed.

(* prove disjunction property. Then we can use the extraction. *)
  
Section sequential_consistency.
Parameter shmem th0 th1: agent.
Axiom sequential_consistency:
  forall (phi psi: o) (u: U),
    judgement u
    (vee (supset (knowledge shmem phi) (knowledge shmem psi))
      (supset (knowledge shmem psi) (knowledge shmem phi))).


Lemma Cleft:
  forall (phi psi: o) (u: U) (ei bee: agent),
    (judgement u
      (supset
        (knowledge ei (knowledge shmem (knowledge ei phi)))
        (knowledge ei (knowledge shmem (knowledge bee psi))))) ->
    (judgement u
      (wedge
        (knowledge ei (knowledge shmem (knowledge ei phi)))
        (knowledge bee (knowledge shmem (knowledge bee psi))))) ->
    (judgement u
      (knowledge ei (knowledge shmem (knowledge bee psi)))).
  intros phi psi u ei bee.
  intro one.
  intro two.
  apply supsetE with (knowledge ei (knowledge shmem (knowledge ei phi))).
  exact one.
  apply wedgeEl with (knowledge bee (knowledge shmem (knowledge bee psi))).
  exact two.
  Qed.

Lemma C:
  forall (phi psi: o) (u: U) (ei bee:agent),
    (judgement u
      (supset
        (knowledge ei (knowledge shmem (knowledge ei phi)))
        (knowledge ei (knowledge shmem (knowledge bee psi))))) ->
    (judgement u
      (wedge
        (knowledge ei (knowledge shmem (knowledge ei phi)))
        (knowledge bee (knowledge shmem (knowledge bee psi))))) ->
    (judgement u
      (knowledge ei (knowledge bee psi))).
  intros phi psi u ei bee.
  intros one two.
  apply supsetE with (knowledge ei (knowledge shmem (knowledge bee psi))).
  apply supsetI.
  intro zero.
  apply kI with ((knowledge shmem (knowledge bee psi)) :: nil).
  intro psi0.
  intro contain.
  induction contain.
  rewrite <- H.
  exact zero.
  apply False_ind.
  apply H.
  intro v.
  intro psi0.
  apply kE with shmem.
  apply kE with ei.
  apply psi0.
  apply in_eq.
  apply Cleft with phi.
  exact one.
  exact two.
  Qed.

Lemma Aright:
  forall (phi psi: o) (u: U) (th0 th1: agent),
    (judgement u (knowledge th0 (knowledge shmem (knowledge th0 phi)))) ->
    (judgement u
      (supset
        (knowledge th0 (supset
          (knowledge shmem (knowledge th0 phi))
          (knowledge shmem (knowledge th1 psi))))
        (knowledge th0 (knowledge shmem (knowledge th1 psi))))).
  intros phi psi u ei bee.
  intro hidari.
  apply supsetI.
  intro two.
  apply kI with ((knowledge shmem (knowledge ei phi)) ::
    (supset (knowledge shmem (knowledge ei phi))
                (knowledge shmem (knowledge bee psi))) :: nil).
  intro psi0.
  intro contain.
  induction contain.
  rewrite <- H.
  exact hidari.
  induction H.
  rewrite <- H.
  exact two.
  apply False_ind.
  apply H.
  intro v.
  intro gamma.
  apply supsetE with (knowledge shmem (knowledge ei phi)).
  apply kE with ei.
  apply gamma.
  apply in_cons.
  apply in_eq.
  apply kE with ei.
  apply gamma.
  apply in_eq.
  Qed.

Lemma Aone:
  forall (phi psi: o) (u: U) (ei bee: agent),
    (judgement u
      (knowledge bee (knowledge ei (supset
        (knowledge shmem (knowledge ei phi))
        (knowledge shmem (knowledge bee psi)))))) ->
    (judgement u (vee
      (supset
        (knowledge ei (knowledge shmem (knowledge ei phi)))
        (knowledge ei (knowledge shmem (knowledge bee psi))))
      (supset
        (knowledge bee (knowledge shmem (knowledge bee psi)))
        (knowledge bee (knowledge shmem (knowledge ei phi)))))).
  intros phi psi u ei bee.
  intro pre.
  apply veeIl.
  apply supsetI.
  intro two.
  apply supsetE with
    (knowledge ei (supset
      (knowledge shmem (knowledge ei phi))
      (knowledge shmem (knowledge bee psi)))).
  apply Aright.
  exact two.
  apply kE with bee.
  exact pre.
  Qed.

Lemma Atwo:
  forall (phi psi: o) (u: U) (ei bee: agent),
    (judgement u
      (knowledge bee (knowledge ei (supset
        (knowledge shmem (knowledge ei phi))
        (knowledge shmem (knowledge bee psi)))))) ->
    (judgement u (vee
      (supset
        (knowledge ei (knowledge shmem (knowledge ei phi)))
        (knowledge ei (knowledge shmem (knowledge bee psi))))
      (supset
        (knowledge bee (knowledge shmem (knowledge bee psi)))
        (knowledge bee (knowledge shmem (knowledge ei phi)))))).
  intros phi psi u ei bee.
  intro pre.
  apply veeIl.
  apply supsetI.
  intro two.
  apply supsetE with (knowledge ei
    (supset (knowledge shmem (knowledge ei phi))
      (knowledge shmem (knowledge bee psi)))).
  apply Aright.
  exact two.
  apply kE with bee.
  exact pre.
  Qed.


Lemma B:
  forall (phi psi: o) (u: U),
    (judgement u
      (vee
        (supset
          (knowledge th0 (knowledge shmem (knowledge th0 phi)))
          (knowledge th0 (knowledge shmem (knowledge th1 psi))))
        (supset
          (knowledge th1 (knowledge shmem (knowledge th1 psi)))
          (knowledge th1 (knowledge shmem (knowledge th0 phi)))))).
  intros phi psi u.
  apply veeE with 
    (knowledge th1 (knowledge th0 (supset
        (knowledge shmem (knowledge th0 phi))
        (knowledge shmem (knowledge th1 psi)))))
    (knowledge th1 (knowledge th0 (supset
        (knowledge shmem (knowledge th1 psi))
        (knowledge shmem (knowledge th0 phi))))).
  apply simplerKvee.
  apply kI with nil.
  intro psi0.
  apply False_ind.
  intro v.
  intro irrelevant.
  apply simplerKvee.
  apply kI with nil.
  intro psi0.
  apply False_ind.
  intro v0.
  intro irre.
  apply sequential_consistency.
  apply Aone.
  intro pre.
  apply veeIr.
  apply supsetI.
  intro two.
  apply supsetE with (knowledge th1 (supset
    (knowledge shmem (knowledge th1 psi))
    (knowledge shmem (knowledge th0 phi)))).
  apply Aright.
  exact two.
  apply kI with ((knowledge th0
                (supset (knowledge shmem (knowledge th1 psi))
                   (knowledge shmem (knowledge th0 phi)))) :: nil).
  intro psi0.
  intro contain.
  induction contain.
  rewrite <- H.
  exact pre.
  apply False_ind.
  apply H.
  intro v.
  intro gamma.
  apply kE with th0.
  apply kE with th1.
  apply gamma.
  apply in_eq.
  Qed.

Lemma fig2:
  forall (phi psi: o) (u: U),
    (judgement u
      (supset
        (wedge
          (knowledge th0 (knowledge shmem (knowledge th0 phi)))
          (knowledge th1 (knowledge shmem (knowledge th1 psi))))
        (vee
          (knowledge th0 (knowledge th1 psi))
          (knowledge th1 (knowledge th0 phi))))).
  intros phi psi u.
  apply supsetI.
  intro pre.
apply veeE with 
  (supset
    (knowledge th0 (knowledge shmem (knowledge th0 phi)))
    (knowledge th0 (knowledge shmem (knowledge th1 psi))))
  (supset
    (knowledge th1 (knowledge shmem (knowledge th1 psi)))
    (knowledge th1 (knowledge shmem (knowledge th0 phi)))).
apply B.
intro two.
apply veeIl.
apply C with phi.
exact two.
exact pre.
intro two.
apply veeIr.
apply C with psi.
exact two.
apply wedgeI.
apply wedgeEr with (knowledge th0 (knowledge shmem (knowledge th0 phi))).
exact pre.
apply wedgeEl with (knowledge th1 (knowledge shmem (knowledge th1 psi))).
exact pre.
Qed.

(* extraction of fig2 yields () *)

Axiom write0:
  forall (psi: o) (u: U),
  judgement u (knowledge th0 psi) ->
  judgement u (knowledge th0 (knowledge shmem (knowledge th0 psi))).
Axiom write1:
  forall (psi: o) (u: U),
    judgement u (knowledge th1 psi) ->
    judgement u (knowledge th1 (knowledge shmem (knowledge th1 psi))).


Lemma comm:
  forall (phi psi: o) (u:U),
    judgement u (knowledge th0 phi) ->
    judgement u (knowledge th1 psi) ->
    judgement u (vee
      (knowledge th0 psi)
      (knowledge th1 phi)).
  intros phi psi u.
  intro one.
  intro two.
  apply veeE with (knowledge th0 (knowledge th1 psi)) (knowledge th1 (knowledge th0 phi)).
  apply supsetE with
        (wedge
          (knowledge th0 (knowledge shmem (knowledge th0 phi)))
          (knowledge th1 (knowledge shmem (knowledge th1 psi)))).
  apply fig2.
  apply wedgeI.
  apply write0.
  exact one.
  apply write1.
  exact two.
  intro pre.
  apply veeIl.
  apply kI with ((knowledge th1 psi) :: nil).
  intro psi0.
  intro contain.
  induction contain.
  rewrite <- H.
  exact pre.
  apply False_ind.
  apply H.
  intro v.
  intro gamma.
  apply kE with th1.
  apply kE with th0.
  apply gamma.
  apply in_eq.
  intro pre.
  apply veeIr.
  apply kI with ((knowledge th0 phi) :: nil).
  intro psi0.
  intro contain.
  induction contain.
  rewrite <- H.
  exact pre.
  apply False_ind.
  apply H.
  intro v.
  intro gamma.
  apply kE with th0.
  apply kE with th1.
  apply gamma.
  apply in_eq.
  Qed.

End sequential_consistency.



Extraction Language Haskell.
Extraction comm.
          
