(* Avron et al. Encoding Modal Logics in Logical Frameworks *)
Parameter agent : Set.

Require Import List.

Parameter U : Type.
Parameter current: U.

Definition o:= U -> Set.

(* Syntax *)
Definition embed (S:Set) (_:U) := S.

Parameter knowledge : agent -> o -> o.
Definition vee (phi:o) (psi:o) (u:U): Set :=
  (sum (phi u)(psi u)).
Definition wedge (phi:o) (psi:o) (u:U): Set :=
  (prod (phi u)(psi u)).
Definition supset (phi:o) (psi:o) (u:U): Set :=
  (phi u) -> (psi u).

Require Import Coq.Sets.Uniset.
Definition ff (u:U) := Emptyset.

(* Model Property *)


Lemma mp:
  forall P Q: Set,
    (P -> Q) -> (forall u: U, (embed P) u -> (embed Q) u).
intros P Q.
intro orig.
intro u.
intro x.
exact (orig x).
Qed.

(* Proof Rules *)
Axiom kE: forall phi: o, forall u: U, forall a: agent,
  (knowledge a phi) u -> phi u.

Axiom kI: forall phi psi: o, forall u: U, forall a: agent,
  (knowledge a psi) u ->
  (forall v: U, ((knowledge a psi) v)
    -> phi v) ->
  (knowledge a phi) u.

Axiom kI2: forall phi psi0 psi1: o, forall u: U, forall a: agent,
  (knowledge a psi0) u -> (knowledge a psi1) u ->
  (forall v: U, (knowledge a psi0) v -> (knowledge a psi1) v
    -> phi v) ->
  (knowledge a phi) u.

Axiom kI0: forall phi: o, forall u: U, forall a: agent,
  (forall v: U, phi v) ->
  (knowledge a phi) u.

Lemma veeIl: forall phi:o, forall psi:o, forall u:U,
  phi u -> (vee phi psi) u.
intros phi psi u.
intro orig.
left.
exact orig.
Qed.

Lemma veeIr: forall phi:o, forall psi:o, forall u:U,
  psi u -> (vee phi psi) u.
intros phi psi u.
intro orig.
right.
exact orig.
Qed.

Lemma veeE: forall phi:o, forall psi:o, forall theta:o, forall u: U,
  (vee phi psi) u ->
  (phi u -> theta u) ->
  (psi u -> theta u) ->
  theta u.
intros phi psi theta u.
intros disj le ri.
case disj.
exact le.
exact ri.
Qed.

Lemma wedgeI: forall phi:o, forall psi:o, forall u: U,
  phi u ->
  psi u ->
  (wedge phi psi) u.
intros phi psi u.
intro one.
intro two.
split.
exact one.
exact two.
Qed.

Lemma wedgeEl: forall phi:o, forall psi:o, forall u:U,
  (wedge phi psi) u ->
  phi u.
intros phi psi u.
intro orig.
elim orig.
intro one.
intro irrelevant.
exact one.
Qed.

Lemma wedgeEr: forall phi:o, forall psi:o, forall u:U,
  (wedge phi psi) u ->
  psi u.
intros phi psi u.
intro orig.
elim orig.
intro irrelevant.
intro two.
exact two.
Qed.

Lemma supsetI: forall phi:o, forall psi:o, forall u:U,
  (phi u -> psi u) -> (supset phi psi) u.
intros phi psi u.
intro orig.
exact orig.
Qed.

Lemma supsetE: forall phi:o, forall psi:o, forall u:U,
  (supset phi psi) u->
  phi u ->
  psi u.
intros phi psi u.
intro orig.
exact orig.
Qed.

Axiom Kvee: forall phi:o, forall psi:o, forall theta:o, forall u:U, forall a:agent,
  (knowledge a (vee phi psi)) u ->
  ((knowledge a phi) u -> theta u) ->
  ((knowledge a psi) u -> theta u) ->
  theta u.

Lemma disj_current: forall (phi psi: o),
  (vee phi psi) current ->
  phi current +  psi current.
  intros phi psi.
  intro pre.
  exact pre.
  Qed.

Lemma skk: forall (u:U) (phi:o),
  (supset phi phi) u.
  intro u.
  intro phi.
  apply supsetI.
  intro one.
  exact one.
  Qed.

Lemma knows_skk:  forall (u:U) (phi:o) (a:agent),
  (knowledge a (supset phi phi)) u.
  intro u.
  intro phi.
  intro a.
  apply kI0.
  intro v.
  apply skk.
  Qed.

Lemma kv: forall (u:U) (phi psi:o) (a:agent),
  (supset
    (knowledge a (vee phi psi))
    (vee (knowledge a phi) (knowledge a psi))) u.
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
      ((vee (embed L) (embed M) u) ->
        ((embed (L+M)) u))).
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
    ((knowledge a (vee phi psi)) u) ->
    ((vee (knowledge a phi)
      (knowledge a psi)) u).
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
    (vee (supset (knowledge shmem phi) (knowledge shmem psi))
      (supset (knowledge shmem psi) (knowledge shmem phi))) u.


Lemma Cleft:
  forall (phi psi: o) (u: U) (ei bee: agent),
    (
      (supset
        (knowledge ei (knowledge shmem (knowledge ei phi)))
        (knowledge ei (knowledge shmem (knowledge bee psi)))) u) ->
    (
      (wedge
        (knowledge ei (knowledge shmem (knowledge ei phi)))
        (knowledge bee (knowledge shmem (knowledge bee psi)))) u) ->
    (
      (knowledge ei (knowledge shmem (knowledge bee psi))) u).
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
    (
      (supset
        (knowledge ei (knowledge shmem (knowledge ei phi)))
        (knowledge ei (knowledge shmem (knowledge bee psi)))) u) ->
    (
      (wedge
        (knowledge ei (knowledge shmem (knowledge ei phi)))
        (knowledge bee (knowledge shmem (knowledge bee psi)))) u) ->
    (
      (knowledge ei (knowledge bee psi)) u).
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
    ((knowledge th0 (knowledge shmem (knowledge th0 phi))) u) ->
    (
      (supset
        (knowledge th0 (supset
          (knowledge shmem (knowledge th0 phi))
          (knowledge shmem (knowledge th1 psi))))
        (knowledge th0 (knowledge shmem (knowledge th1 psi)))) u).
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
    (
      (knowledge bee (knowledge ei (supset
        (knowledge shmem (knowledge ei phi))
        (knowledge shmem (knowledge bee psi))))) u) ->
    ((vee
      (supset
        (knowledge ei (knowledge shmem (knowledge ei phi)))
        (knowledge ei (knowledge shmem (knowledge bee psi))))
      (supset
        (knowledge bee (knowledge shmem (knowledge bee psi)))
        (knowledge bee (knowledge shmem (knowledge ei phi))))) u).
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
    (
      (knowledge bee (knowledge ei (supset
        (knowledge shmem (knowledge ei phi))
        (knowledge shmem (knowledge bee psi))))) u) ->
    ((vee
      (supset
        (knowledge ei (knowledge shmem (knowledge ei phi)))
        (knowledge ei (knowledge shmem (knowledge bee psi))))
      (supset
        (knowledge bee (knowledge shmem (knowledge bee psi)))
        (knowledge bee (knowledge shmem (knowledge ei phi))))) u).
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
    (
      (vee
        (supset
          (knowledge th0 (knowledge shmem (knowledge th0 phi)))
          (knowledge th0 (knowledge shmem (knowledge th1 psi))))
        (supset
          (knowledge th1 (knowledge shmem (knowledge th1 psi)))
          (knowledge th1 (knowledge shmem (knowledge th0 phi))))) u).
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
    (
      (supset
        (wedge
          (knowledge th0 (knowledge shmem (knowledge th0 phi)))
          (knowledge th1 (knowledge shmem (knowledge th1 psi))))
        (vee
          (knowledge th0 (knowledge th1 psi))
          (knowledge th1 (knowledge th0 phi)))) u).
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
  (knowledge th0 psi) u->
   (knowledge th0 (knowledge shmem (knowledge th0 psi))) u.
Axiom write1:
  forall (psi: o) (u: U),
     (knowledge th1 psi) u ->
     (knowledge th1 (knowledge shmem (knowledge th1 psi))) u.


Lemma comm:
  forall (phi psi: o) (u:U),
    (knowledge th0 phi) u ->
    (knowledge th1 psi) u ->
    (vee
      (knowledge th0 psi)
      (knowledge th1 phi)) u .
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
     (knowledge th0 phi) current ->
     (knowledge th1 psi) current ->
    ( (knowledge th0 psi) current +
     (knowledge th1 phi) current).
intros phi psi.
intros one two.
apply disj_current.
apply comm.
exact one.
exact two.
Qed.

Lemma motto_comm:
  forall (L M: Set),
     (knowledge th0 (embed L)) current ->
 (knowledge th1 (embed M)) current ->
    ( (knowledge th0 (embed M)) current +
      (knowledge th1 (embed L)) current).
  intros L M.
apply more_comm.
Qed.


End sequential_consistency.

Extraction Language Haskell.
Extraction motto_comm.
Extraction more_comm.
Extraction comm.
Extraction fig2.
Extraction B.

(* TODO: replace vee, wedge, and supset with native Coq connectives.
   and make rules for those constants lemmas not axioms. *)

