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
Defined.

(* Proof Rules *)
Axiom kE: forall phi: o, forall u: U, forall a: agent,
  (knowledge a phi) u -> phi u.

Axiom kI0: forall phi: o, forall u: U, forall a: agent,
  (forall v: U, phi v) ->
  (knowledge a phi) u.

Section kEkI0.
  Variable s:Set.
  Variable x: s.
  Lemma pr: forall v:U, (embed s) v.
    intro v.
    compute.
    exact x.
  Defined.
  Print pr.
  Variable a: agent.
  Axiom kEkI0: kE (embed s) current a (kI0 (embed s) current a pr) = x.
End kEkI0.

Parameter shmem th0 th1: agent.

Definition owned (a:agent) := knowledge (a:agent) (embed nat) current.
Definition look0 (n:owned th0) := kE (embed nat) current th0 n.
Definition look1 (n:owned th1) := kE (embed nat) current th1 n.
Definition look (n:(owned th0 + owned th1)) :=
  match n with
      inl n => look0 n
    | inr n => look1 n
  end.

Definition zero0: owned th0.
  apply kI0.
  intro v.
  exact O.
  Defined.

Definition back: nat.
  exact (kE (embed nat) current th0 zero0).
  Defined.

Lemma backzero: back = O.
  apply kEkI0.
  Qed.

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


Lemma veeIl: forall phi:o, forall psi:o, forall u:U,
  phi u -> (vee phi psi) u.
intros phi psi u.
intro orig.
left.
exact orig.
Defined.

Lemma veeIr: forall phi:o, forall psi:o, forall u:U,
  psi u -> (vee phi psi) u.
intros phi psi u.
intro orig.
right.
exact orig.
Defined.

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
Defined.

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
Defined.

Lemma wedgeEl: forall phi:o, forall psi:o, forall u:U,
  (wedge phi psi) u ->
  phi u.
intros phi psi u.
intro orig.
elim orig.
intro one.
intro irrelevant.
exact one.
Defined.

Lemma wedgeEr: forall phi:o, forall psi:o, forall u:U,
  (wedge phi psi) u ->
  psi u.
intros phi psi u.
intro orig.
elim orig.
intro irrelevant.
intro two.
exact two.
Defined.

Lemma supsetI: forall phi:o, forall psi:o, forall u:U,
  (phi u -> psi u) -> (supset phi psi) u.
intros phi psi u.
intro orig.
exact orig.
Defined.

Lemma supsetE: forall phi:o, forall psi:o, forall u:U,
  (supset phi psi) u->
  phi u ->
  psi u.
intros phi psi u.
intro orig.
exact orig.
Defined.

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
Defined.

Lemma skk: forall (u:U) (phi:o),
  (supset phi phi) u.
  intro u.
  intro phi.
  apply supsetI.
  intro one.
  exact one.
Defined.

Lemma knows_skk:  forall (u:U) (phi:o) (a:agent),
  (knowledge a (supset phi phi)) u.
  intro u.
  intro phi.
  intro a.
  apply kI0.
  intro v.
  apply skk.
Defined.

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
Defined.


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
Defined.

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
Defined.

(* prove disjunction property. Then we can use the extraction. *)
  
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
Defined.

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
Defined.

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
Defined.

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
Defined.

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
Defined.


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
Defined.

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
Defined.

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
Defined.

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
Defined.

Lemma motto_comm:
  forall (L M: Set),
     (knowledge th0 (embed L)) current ->
     (knowledge th1 (embed M)) current ->
    ( (knowledge th0 (embed M)) current +
      (knowledge th1 (embed L)) current).
  intros L M.
  apply more_comm.
Defined.


(* just in order to ensure the type of look0, look1 
Parameter possess0: nat -> owned th0.
Parameter possess1: nat -> owned th1.
Axiom lp0: forall n:nat, look0 (possess0 n) = n.
Axiom lp1: forall n:nat, look1 (possess1 n) = n.
*)

Axiom ask_user0: owned th0.
Axiom ask_user1: owned th1.

Check kI.
Check kI (embed nat) (embed nat) current th0.
Check kI (embed nat) (embed nat) current th0 ask_user0.

Section remote_calc.
  Parameter f: nat->nat.
  Check kI (embed nat) (embed nat) current th0 ask_user0.
End remote_calc.

(* make calc0 not parameter, but a defined object *)

Lemma add0: owned th0 -> (owned th0) -> (owned th0).
  intros one two.
  apply kI2 with (embed nat) (embed nat).
  exact one.
  exact two.
  intro v.
  intros one_in two_in.
  exact ((kE (embed nat) v th0 one_in) + (kE (embed nat) v th0 two_in)).
Defined.

Lemma add1: owned th1 -> (owned th1) -> (owned th1).
  intros one two.
  apply kI2 with (embed nat) (embed nat).
  exact one.
  exact two.
  intro v.
  intros one_in two_in.
  exact ((kE (embed nat) v th1 one_in) + (kE (embed nat) v th1 two_in)).
Defined.


(* value exchanging preserves value *)
Section changed.
  Variable n0: owned th0.
  Variable n1: owned th1.
  Definition ex := motto_comm nat nat n0 n1.
  Check ex.
  Lemma lefthand:
    forall n: owned th0, 
    (ex = inl (owned th1) n) -> look0 n = look0 n0.
    intro n.


Definition exchanged :=
  (motto_comm nat nat ask_user0 ask_user1).

Definition ex_type :=
  (sum (knowledge th0 (embed nat) current) (knowledge th1 (embed nat) current)).

Check exchanged: ex_type.
Check exchanged: owned th0 + owned th1.
Check inl.

Definition add_own (e:ex_type) : ex_type :=
  match e with
    inl e => inl (owned th1) (add0 e ask_user0)
  | inr e => inr (owned th0) (add1 e ask_user1)
  end.

Require Import Setoid.
Lemma sum_calc:
  (exists n: (owned th0 + owned th1),
    look n = (look0 ask_user0) + (look1 ask_user1)).
  exists (add_own exchanged).
  compute -[plus].

Extraction Language Haskell.

Extract Constant current => "()".
Extract Constant kE => "\x->x".
Extract Constant agent => "Agent".
Extract Constant knowledge "'data" => "'data".

Recursive Extraction motto_comm.

