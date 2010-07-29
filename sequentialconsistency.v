(* Avron et al. Encoding Modal Logics in Logical Frameworks *)

Parameter agent : Set.

Require Import List.

Parameter U : Type.
Parameter current: U.

Parameter o: Type.

(* Model Properties *)
Parameter paraset: U -> o -> Set.

(* Syntax *)
Parameter embed : Set -> o.
Parameter knowledge : agent -> o -> o.
Parameter vee: o->o->o.
Parameter wedge: o->o->o.
Parameter supset: o->o->o.
Parameter ff: o.

(* Model Property *)
Axiom valid: forall S: Set,
  forall u:U, S -> paraset u (embed S).

Axiom back: forall S: Set,
  paraset current (embed S) -> S.

Axiom validback:
  forall S: Set, forall x: S, back S (valid S current x) = x.

Axiom mp:
  forall P Q: Set,
    (P -> Q) -> (forall u: U, paraset u (embed P) -> paraset u (embed Q)).

(* Proof Rules *)
Axiom kE: forall phi: o, forall u: U, forall a: agent,
  paraset u (knowledge a phi) -> paraset u phi.

Axiom kI: forall phi psi: o, forall u: U, forall a: agent,
  paraset u (knowledge a psi) ->
  (forall v: U, (paraset v (knowledge a psi))
    -> paraset v phi) ->
  paraset u (knowledge a phi).

Axiom kI2: forall phi psi0 psi1: o, forall u: U, forall a: agent,
  paraset u (knowledge a psi0) -> paraset u (knowledge a psi1) ->
  (forall v: U, (paraset v (knowledge a psi0)) -> (paraset v (knowledge a psi1))
    -> paraset v phi) ->
  paraset u (knowledge a phi).

Axiom kI0: forall phi: o, forall u: U, forall a: agent,
  (forall v: U, paraset v phi) ->
  paraset u (knowledge a phi).

Axiom veeIl: forall phi:o, forall psi:o, forall u:U,
  paraset u phi -> paraset u (vee phi psi).

Axiom veeIr: forall phi:o, forall psi:o, forall u:U,
  paraset u psi -> paraset u (vee phi psi).

Axiom veeE: forall phi:o, forall psi:o, forall theta:o, forall u: U,
  paraset u (vee phi psi) ->
  (paraset u phi -> paraset u theta) ->
  (paraset u psi -> paraset u theta) ->
  paraset u theta.

Axiom wedgeI: forall phi:o, forall psi:o, forall u: U,
  paraset u phi ->
  paraset u psi ->
  paraset u (wedge phi psi).

Axiom wedgeEl: forall phi:o, forall psi:o, forall u:U,
  paraset u (wedge phi psi) ->
  paraset u phi.

Axiom wedgeEr: forall phi:o, forall psi:o, forall u:U,
  paraset u (wedge phi psi) ->
  paraset u psi.

Axiom supsetI: forall phi:o, forall psi:o, forall u:U,
  (paraset u phi -> paraset u psi) -> paraset u (supset phi psi).

Axiom supsetE: forall phi:o, forall psi:o, forall u:U,
  paraset u (supset phi psi) ->
  paraset u phi ->
  paraset u psi.

Axiom Kvee: forall phi:o, forall psi:o, forall theta:o, forall u:U, forall a:agent,
  paraset u (knowledge a (vee phi psi)) ->
  (paraset u (knowledge a phi) -> paraset u theta) ->
  (paraset u (knowledge a psi) -> paraset u theta) ->
  paraset u theta.


Lemma disj_current_embed: forall (L M: Set),
  paraset current (vee (embed L) (embed M)) ->
  paraset current (embed L) +
  paraset current (embed M).
  intros L M.
  intro pre.
  apply back.
  apply veeE with (embed L) (embed M).
  exact pre.
  apply mp.
  left.
  apply valid.
  exact H.
  apply mp.
  right.
  apply valid.
  exact H.
  Qed.

Lemma disj_current: forall (phi psi: o),
  paraset current (vee phi psi) ->
  paraset current phi + paraset current psi.
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


Lemma everywhere00: forall u:U, paraset u (embed (0 = 0)).
intro u.
apply valid.
reflexivity.
Qed.

Lemma everywherek00: forall u:U, forall a:agent,
  paraset u (knowledge a (embed (0 = 0))).
intro u.
intro a.
apply kI0.
intro v.
apply valid.
reflexivity.
Qed.

Print everywherek00.
Print False_ind.

Lemma skk: forall (u:U) (phi:o),
  paraset u (supset phi phi).
  intro u.
  intro phi.
  apply supsetI.
  auto.
  Qed.

Lemma knows_skk:  forall (u:U) (phi:o) (a:agent),
  paraset u (knowledge a (supset phi phi)).
  intro u.
  intro phi.
  intro a.
  apply kI0.
  intro v.
  apply skk.
  Qed.

Lemma kv: forall (u:U) (phi psi:o) (a:agent),
  paraset u (supset
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


Lemma disj_distr:
  forall L M:Set,
    (forall (u:U),
      (paraset u (vee (embed L) (embed M)) ->
        (paraset u (embed (L+M))))).
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

Lemma simplerKvee:
  forall (u: U) (phi psi: o) (a:agent),
    (paraset u (knowledge a (vee phi psi))) ->
    (paraset u (vee (knowledge a phi)
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
    paraset u
    (vee (supset (knowledge shmem phi) (knowledge shmem psi))
      (supset (knowledge shmem psi) (knowledge shmem phi))).


Lemma Cleft:
  forall (phi psi: o) (u: U) (ei bee: agent),
    (paraset u
      (supset
        (knowledge ei (knowledge shmem (knowledge ei phi)))
        (knowledge ei (knowledge shmem (knowledge bee psi))))) ->
    (paraset u
      (wedge
        (knowledge ei (knowledge shmem (knowledge ei phi)))
        (knowledge bee (knowledge shmem (knowledge bee psi))))) ->
    (paraset u
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
    (paraset u
      (supset
        (knowledge ei (knowledge shmem (knowledge ei phi)))
        (knowledge ei (knowledge shmem (knowledge bee psi))))) ->
    (paraset u
      (wedge
        (knowledge ei (knowledge shmem (knowledge ei phi)))
        (knowledge bee (knowledge shmem (knowledge bee psi))))) ->
    (paraset u
      (knowledge ei (knowledge bee psi))).
  intros phi psi u ei bee.
  intros one two.
  apply supsetE with (knowledge ei (knowledge shmem (knowledge bee psi))).
  apply supsetI.
  intro zero.
  apply kI with (knowledge shmem (knowledge bee psi)).
  exact zero.
  intro v.
  intro psi0.
  apply kE with shmem.
  apply kE with ei.
  exact psi0.
  apply Cleft with phi.
  exact one.
  exact two.
  Qed.

Lemma Aright:
  forall (phi psi: o) (u: U) (th0 th1: agent),
    (paraset u (knowledge th0 (knowledge shmem (knowledge th0 phi)))) ->
    (paraset u
      (supset
        (knowledge th0 (supset
          (knowledge shmem (knowledge th0 phi))
          (knowledge shmem (knowledge th1 psi))))
        (knowledge th0 (knowledge shmem (knowledge th1 psi))))).
  intros phi psi u ei bee.
  intro hidari.
  apply supsetI.
  intro two.
  apply kI2 with (knowledge shmem (knowledge ei phi))
    (supset (knowledge shmem (knowledge ei phi))
                (knowledge shmem (knowledge bee psi))).
  exact hidari.
  exact two.
  intro v.
  intro gamma.
  intro deltan.
  apply supsetE with (knowledge shmem (knowledge ei phi)).
  apply kE with ei.
  apply deltan.
  apply kE with ei.
  apply gamma.
  Qed.

Lemma Aone:
  forall (phi psi: o) (u: U) (ei bee: agent),
    (paraset u
      (knowledge bee (knowledge ei (supset
        (knowledge shmem (knowledge ei phi))
        (knowledge shmem (knowledge bee psi)))))) ->
    (paraset u (vee
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
    (paraset u
      (knowledge bee (knowledge ei (supset
        (knowledge shmem (knowledge ei phi))
        (knowledge shmem (knowledge bee psi)))))) ->
    (paraset u (vee
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
    (paraset u
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
  apply kI0.
  intro v.
  apply simplerKvee.
  apply kI0.
  intro v0.
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
  apply kI with (knowledge th0
                (supset (knowledge shmem (knowledge th1 psi))
                   (knowledge shmem (knowledge th0 phi)))).
  exact pre.
  intro v.
  intro gamma.
  apply kE with th0.
  apply kE with th1.
  apply gamma.
  Qed.

Lemma fig2:
  forall (phi psi: o) (u: U),
    (paraset u
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
  paraset u (knowledge th0 psi) ->
  paraset u (knowledge th0 (knowledge shmem (knowledge th0 psi))).
Axiom write1:
  forall (psi: o) (u: U),
    paraset u (knowledge th1 psi) ->
    paraset u (knowledge th1 (knowledge shmem (knowledge th1 psi))).


Lemma comm:
  forall (phi psi: o) (u:U),
    paraset u (knowledge th0 phi) ->
    paraset u (knowledge th1 psi) ->
    paraset u (vee
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
  apply kI with (knowledge th1 psi).
  exact pre.
  intro v.
  intro gamma.
  apply kE with th1.
  apply kE with th0.
  apply gamma.
  intro pre.
  apply veeIr.
  apply kI with (knowledge th0 phi).
  exact pre.
  intro v.
  intro gamma.
  apply kE with th0.
  apply kE with th1.
  apply gamma.
  Qed.

Lemma more_comm:
  forall (phi psi: o),
    paraset current (knowledge th0 phi) ->
    paraset current (knowledge th1 psi) ->
    (paraset current (knowledge th0 psi) +
    paraset current (knowledge th1 phi)).
intros phi psi.
intros one two.
apply disj_current.
apply comm.
exact one.
exact two.
Qed.

Lemma motto_comm:
  forall (L M: Set),
    paraset current (knowledge th0 (embed L)) ->
    paraset current (knowledge th1 (embed M)) ->
    (paraset current (knowledge th0 (embed M)) +
     paraset current (knowledge th1 (embed L))).
  intros L M.
apply more_comm.
Qed.


End sequential_consistency.

Extraction Language Haskell.
Extraction motto_comm.
Extraction more_comm.
Extraction comm.

(* TODO: replace vee, wedge, and supset with native Coq connectives.
   and make rules for those constants lemmas not axioms. *)




          
