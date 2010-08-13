(* Avron et al. Encoding Modal Logics in Logical Frameworks *)
Parameter agent : Set.

Require Import List.

Parameter U : Type.
Parameter current: U.
Parameter io: Set -> Set.

Parameter ret: forall (S:Set), S -> io S.
Parameter bind: forall (S T:Set), io S -> (S -> io T) -> io T.

Definition o:= U -> Set.

(* Syntax *)
Definition embed (S:Set) (_:U) := io S.

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
compute.
apply bind with P.
exact x.
intro y.
apply ret.
apply orig.
exact y.
Defined.

(* Proof Rules *)
Axiom kE: forall phi: o, forall u: U, forall a: agent,
  (knowledge a phi) u -> phi u.

Fixpoint all_knowledge (u:U) (a: agent) (orig:list o) :=
  match orig with
    | nil => unit
    | cons h tl =>
      (prod ((knowledge a h) u) (all_knowledge u a tl))
  end.

Axiom kI: 
  forall (phi:o) (psi: list o) (u:U) (a:agent),
    (all_knowledge u a psi) ->
    (forall (v: U),
      (all_knowledge v a psi) -> phi v) ->
    (knowledge a phi) u.

(* useful macros *)

Definition kI0:
  forall (phi:o) (u:U) (a: agent),
    (forall (v:U), phi v) ->
    (knowledge a phi) u.
intros phi u a pre.
apply kI with nil.
exact tt.
clear u.
intro v.
intro unneeded.
clear unneeded a.
apply pre.
Defined.

Definition kI1:
  forall (phi:o) (psi: o) (u:U) (a:agent)
    (x: (knowledge a psi) u)
    (f: (forall v:U, all_knowledge v a (psi :: nil) -> phi v)),
    (knowledge a phi) u.
intros phi psi u a.
intro x.
intro pre.
apply kI with (psi :: nil).
split.
exact x.
compute.
exact tt.
intro v.
clear u x.
apply pre.
Defined.

Print kI1.

Definition kI2:
  forall (phi psi0 psi1: o) (u:U) (a:agent)
    (x: (knowledge a psi0) u)
    (y: (knowledge a psi1) u)
    (f: (forall v:U, all_knowledge v a (psi0 :: psi1 :: nil) -> phi v)),
    (knowledge a phi) u.
intros phi psi0 psi1 u a pre0 pre1.
intro f.
apply kI with (psi0 :: psi1 :: nil).
split.
exact pre0.
split.
exact pre1.
compute.
exact tt.
intro v.
clear u pre0 pre1.
apply f.
Defined.

Section kEkI.
  Variable u: U.
  Variable phi: o.
  Variable psi: list o.
  Variable a: agent.
  Variable x:
    all_knowledge u a psi.
  Variable f:
    forall (v:U),
      (all_knowledge v a psi -> phi v).
  

  Check kI.
  Check kI phi psi.
  Check kI phi psi u a.
  Check kI phi psi u a x f.
  Check kI phi psi u a x f : knowledge a phi u.
  (* kEkI route *)
  Check kE.
  Check kE phi u a (kI phi psi u a x f) : phi u.

  (* straight route *)
  Check f u.
  Check f u x : phi u.

  (* maybe, we want this = into >= in order to represent the monotonicity *)
  Axiom kEkI: kE phi u a (kI phi psi u a x f) = f u x.
  Hint Resolve kEkI.
End kEkI.

Print kEkI.


Parameter xbox ybox th0 th1: agent.

Definition owned (a:agent) := knowledge (a:agent) (embed nat) current.
Definition look0 (n:owned th0) := kE (embed nat) current th0 n.
Definition look1 (n:owned th1) := kE (embed nat) current th1 n.
Definition look (n:(owned th0 + owned th1)) :=
  match n with
      inl n => look0 n
    | inr n => look1 n
  end.

Definition formalzero : (forall v:U, (embed nat) v).
intro v.
exact (ret nat O).
Defined.

Definition nileater : all_knowledge current th0 nil.
compute.
exact tt.
Defined.

Definition z : forall v:U,
  (all_knowledge v th0 nil) ->
  (embed nat) v.
intros v f.
generalize v.
exact formalzero.
Defined.

Lemma backzero:
  kE (embed nat) current th0 (kI (embed nat) nil current th0 nileater z) =
       formalzero current.
  apply kEkI.
  Qed.


Definition veeIl: forall phi:o, forall psi:o, forall u:U,
  phi u -> (vee phi psi) u.
intros phi psi u.
intro orig.
left.
exact orig.
Defined.

Definition veeIr: forall phi:o, forall psi:o, forall u:U,
  psi u -> (vee phi psi) u.
intros phi psi u.
intro orig.
right.
exact orig.
Defined.

Definition veeE: forall phi:o, forall psi:o, forall theta:o, forall u: U,
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

Definition veeEveeIr:
  forall (phi psi theta:o) (u: U) (x: phi u) (fl: phi u-> theta u) (fr: psi u -> theta u),
    fl x = veeE phi psi theta u (veeIl phi psi u x) fl fr.
  intros phi psi theta u x fl fr.
  compute.
  reflexivity.
Defined.

Definition wedgeI: forall phi:o, forall psi:o, forall u: U,
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

Definition wedgeEl: forall phi:o, forall psi:o, forall u:U,
  (wedge phi psi) u ->
  phi u.
intros phi psi u.
intro orig.
elim orig.
intro one.
intro irrelevant.
exact one.
Defined.

Definition wedgeEr: forall phi:o, forall psi:o, forall u:U,
  (wedge phi psi) u ->
  psi u.
intros phi psi u.
intro orig.
elim orig.
intro irrelevant.
intro two.
exact two.
Defined.

Definition supsetI: forall phi:o, forall psi:o, forall u:U,
  (phi u -> psi u) -> (supset phi psi) u.
intros phi psi u.
intro orig.
exact orig.
Defined.

Definition supsetE: forall phi:o, forall psi:o, forall u:U,
  (supset phi psi) u->
  phi u ->
  psi u.
intros phi psi u.
intro orig.
exact orig.
Defined.

Axiom kV: forall phi:o, forall psi:o, forall theta:o, forall u:U, forall a:agent,
  (knowledge a (vee phi psi)) u ->
  ((knowledge a phi) u -> theta u) ->
  ((knowledge a psi) u -> theta u) ->
  theta u.

Section kVkIveeI.
  Variable phi psi theta:o.
  Variable u:U.
  Variable a:agent.
  Variable chi: list o.
  Variable kchi: all_knowledge u a chi.
  Variable kphi: (forall v:U, all_knowledge v a chi -> phi v).
  Variable kpsi: (forall v:U, all_knowledge v a chi -> psi v).
  Let kphipsiL: (forall v:U, all_knowledge v a chi -> (vee phi psi) v).
  intro v.
  intro source.
  apply veeIl.
  apply kphi.
  apply source.
  Defined.
  Let kphipsiR: (forall v:U, all_knowledge v a chi -> (vee phi psi) v).
  intro v.
  intro source.
  apply veeIr.
  apply kpsi.
  apply source.
  Defined.
  Let origL: (knowledge a (vee phi psi)) u.
  apply kI with chi.
  exact kchi.
  exact kphipsiL.
  Defined.
  Let origR: (knowledge a (vee phi psi)) u.
  apply kI with chi.
  exact kchi.
  exact kphipsiR.
  Defined.
  Variable phichi:
    (knowledge a phi) u -> theta u.
  Variable psichi:
    (knowledge a psi) u -> theta u.

  (* the original route *)
  Let pthetaLorig:
    theta u.
  apply kV with phi psi a.
  exact origL.
  exact phichi.
  exact psichi.
  Defined.
  (* the reduced route *)
  Let pthetaLred: theta u.
  apply phichi.
  apply kI with chi.
  exact kchi.
  exact kphi.
  Defined.
  Axiom kVkIvIl: pthetaLorig = pthetaLred.
  Hint Resolve kVkIvIl.

  (* the original route *)
  Let pthetaRorig:
    theta u.
  apply kV with phi psi a.
  exact origR.
  exact phichi.
  exact psichi.
  Defined.
  (* the reduced route *)
  Let pthetaRred: theta u.
  apply psichi.
  apply kI with chi.
  exact kchi.
  exact kpsi.
  Defined.
  Axiom kVkIvIr: pthetaRorig = pthetaRred.
  Hint Resolve kVkIvIr.

End kVkIveeI.

Print kVkIvIl.
Print kVkIvIr.

Section p4.
  (* Hirai APLAS Permutative conversion 4. *)
  Variable xtype :o.
  Variable ytype :o.
  Variable a: agent.
  Variable u: U.
  Variable M: (vee xtype ytype) u.
  Variable ztype: o.
  Variable N: xtype u -> (knowledge a ztype u).
  Variable O: ytype u -> (knowledge a ztype u).
  Let original: ztype u.
  apply kE with a.
  apply veeE with xtype ytype.
  exact M.
  apply N.
  apply O.
  Defined.
  Let reduced: ztype u.
  apply veeE with xtype ytype.
  exact M.
  intro x.
  apply kE with a.
  apply N.
  exact x.
  intro y.
  apply kE with a.
  apply O.
  exact y.
  Defined.
  Axiom p4: original = reduced.
End p4.

Hint Resolve p4.

Section testvee.
  Variable A B C D: Set.
  Variable x: A + B.
  Variable y: A -> C -> D.
  Variable z: B -> C -> D.
  Variable w: C.
  Let righty: D.
  case x.
  intro a.
  apply y.
  apply a.
  apply w.
  intro b.
  apply z.
  apply b.
  apply w.
  Defined.
  Let leftyC: C->D.
  case x.
  apply y.
  apply z.
  Defined.
  Let lefty: D.
  apply leftyC.
  exact w.
  Defined.
  Lemma testvee: lefty = righty.
    compute.
    case x.
    reflexivity.
    reflexivity.
    Defined.
  End testvee.

(* todo begin here *)
  
Section p5.
  Variable u: U.
  Variable xtype ytype utype vtype resulttype: o.
  Variable M: (vee xtype ytype) u.
  Variable a: agent.
  Variable N: xtype u -> (knowledge a (vee utype vtype)) u.
  Variable O: ytype u -> (knowledge a (vee utype vtype)) u.
  Variable P: knowledge a utype u -> resulttype u.
  Variable Q: knowledge a vtype u -> resulttype u.
  Let orig_inner:
    (knowledge a (vee utype vtype)) u.
  apply veeE with xtype ytype.
  exact M.
  exact N.
  exact O.
  Defined.
  Let orig: resulttype u.
  apply kV with utype vtype a.
  exact orig_inner.
  clear orig_inner.
  exact P.
  exact Q.
  Defined.
  Let reduced: resulttype u.
  apply veeE with xtype ytype.
  exact M.
  intro x.
  apply kV with utype vtype a.
  apply N.
  exact x.
  exact P.
  exact Q.
  intro y.
  apply kV with utype vtype a.
  apply O.
  exact y.
  exact P.
  exact Q.
  Defined.
  Axiom p5: orig = reduced.
  Hint Resolve p5.
End p5.

Section p8.
  Variable u: U.
  Variable xtype ytype: o.
  Variable pinput poutput: o.
  Variable a: agent.
  Variable M: knowledge a (vee xtype ytype) u.
  Variable N: (knowledge a xtype u) -> pinput u.
  Variable O: (knowledge a ytype u) -> pinput u.
  Variable P: pinput u -> poutput u.
  Let orig: poutput u.
  apply P.
  clear P.
  apply kV with xtype ytype a.
  exact M.
  exact N.
  exact O.
  Defined.
  Let reduced: poutput u.
  apply kV with xtype ytype a.
  exact M.
  intro x.
  apply P.
  apply N.
  exact x.
  intro y.
  apply P.
  apply O.
  exact y.
  Defined.
  Axiom p8: orig = reduced.
  Hint Resolve p8.
End p8.

Section p9.
  (* implement *)
End p9.

(* implement 10, 11, 12, 13, 15, 16, 17 *)
  

Lemma disj_current: forall (phi psi: o),
  (vee phi psi) current ->
  phi current +  psi current.
  intros phi psi.
  intro pre.
  exact pre.
Defined.

Lemma skk: forall (u:U) (phi:o),
  (supset phi phi) u.
  intro u0.
  intro phi.
  apply supsetI.
  intro one.
  exact one.
Defined.

Lemma knows_skk:  forall (u:U) (phi:o) (a:agent),
  (knowledge a (supset phi phi)) u.
  intro u0.
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
  apply kV with phi psi a.
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
  apply kV with phi psi a.
  exact pre.
  apply veeIl.
  apply veeIr.
Defined.

(* prove disjunction property. Then we can use the extraction. *)

Axiom sequential_consistency:
  forall (phi psi: o) (u: U),
    (vee (supset (knowledge xbox phi) (knowledge ybox psi))
      (supset (knowledge ybox psi) (knowledge xbox phi))) u.

Axiom xbox_once:
  forall (u:U) (phi:o) (x y:knowledge xbox phi u), x = y.
Hint Resolve xbox_once.
  
Axiom ybox_once:
  forall (u:U) (phi:o) (x y:knowledge ybox phi u), x = y.
Hint Resolve ybox_once.  

Lemma Cleft:
  forall (phi psi: o) (u: U) (ei bee c d: agent),
    (
      (supset
        (knowledge ei (knowledge c (knowledge ei phi)))
        (knowledge ei (knowledge d (knowledge bee psi)))) u) ->
    (
      (wedge
        (knowledge ei (knowledge c (knowledge ei phi)))
        (knowledge bee (knowledge d (knowledge bee psi)))) u) ->
    (
      (knowledge ei (knowledge d (knowledge bee psi))) u).
  intros phi psi u ei bee c d.
  intro one.
  intro two.
  apply supsetE with (knowledge ei (knowledge c (knowledge ei phi))).
  exact one.
  apply wedgeEl with (knowledge bee (knowledge d (knowledge bee psi))).
  exact two.
Defined.

Lemma C:
  forall (phi psi: o) (u: U) (ei bee c d:agent),
    (
      (supset
        (knowledge ei (knowledge c (knowledge ei phi)))
        (knowledge ei (knowledge d (knowledge bee psi)))) u) ->
    (
      (wedge
        (knowledge ei (knowledge c (knowledge ei phi)))
        (knowledge bee (knowledge d (knowledge bee psi)))) u) ->
    (
      (knowledge ei (knowledge bee psi)) u).
  intros phi psi u ei bee c d.
  intros one two.
  apply supsetE with (knowledge ei (knowledge d (knowledge bee psi))).
  apply supsetI.
  intro zero.
  apply kI1 with (knowledge d (knowledge bee psi)).
  exact zero.
  intro v.
  intro psi0.
  apply kE with d.
  apply kE with ei.
  apply psi0.
  apply Cleft with phi c.
  exact one.
  exact two.
Defined.

Lemma Aright:
  forall (phi psi: o) (u: U) (th0 th1: agent),
    ((knowledge th0 (knowledge xbox (knowledge th0 phi))) u) ->
    (
      (supset
        (knowledge th0 (supset
          (knowledge xbox (knowledge th0 phi))
          (knowledge ybox (knowledge th1 psi))))
        (knowledge th0 (knowledge ybox (knowledge th1 psi)))) u).
  intros phi psi u ei bee.
  intro hidari.
  apply supsetI.
  intro two.
  apply kI2 with (knowledge xbox (knowledge ei phi))
    (supset (knowledge xbox (knowledge ei phi))
                (knowledge ybox (knowledge bee psi))).
  exact hidari.
  exact two.
  intro v.
  intro gamma.
  apply supsetE with (knowledge xbox (knowledge ei phi)).
  apply kE with ei.
  apply gamma.
  apply kE with ei.
  apply gamma.
Defined.

Lemma Aright2:
  forall (phi psi: o) (u: U) (th0 th1: agent),
    ((knowledge th0 (knowledge ybox (knowledge th0 phi))) u) ->
    (
      (supset
        (knowledge th0 (supset
          (knowledge ybox (knowledge th0 phi))
          (knowledge xbox (knowledge th1 psi))))
        (knowledge th0 (knowledge xbox (knowledge th1 psi)))) u).
  intros phi psi u ei bee.
  intro hidari.
  apply supsetI.
  intro two.
  apply kI2 with (knowledge ybox (knowledge ei phi))
    (supset (knowledge ybox (knowledge ei phi))
                (knowledge xbox (knowledge bee psi))).
  exact hidari.
  exact two.
  intro v.
  intro gamma.
  apply supsetE with (knowledge ybox (knowledge ei phi)).
  apply kE with ei.
  apply gamma.
  apply kE with ei.
  apply gamma.
Defined.

Lemma Aone:
  forall (phi psi: o) (u: U) (ei bee: agent),
    (
      (knowledge bee (knowledge ei (supset
        (knowledge xbox (knowledge ei phi))
        (knowledge ybox (knowledge bee psi))))) u) ->
    ((vee
      (supset
        (knowledge ei (knowledge xbox (knowledge ei phi)))
        (knowledge ei (knowledge ybox (knowledge bee psi))))
      (supset
        (knowledge bee (knowledge ybox (knowledge bee psi)))
        (knowledge bee (knowledge xbox (knowledge ei phi))))) u).
  intros phi psi u ei bee.
  intro pre.
  apply veeIl.
  apply supsetI.
  intro two.
  apply supsetE with
    (knowledge ei (supset
      (knowledge xbox (knowledge ei phi))
      (knowledge ybox (knowledge bee psi)))).
  apply Aright.
  exact two.
  apply kE with bee.
  exact pre.
Defined.

Lemma Atwo:
  forall (phi psi: o) (u: U) (ei bee: agent),
    (
      (knowledge bee (knowledge ei (supset
        (knowledge xbox (knowledge ei phi))
        (knowledge ybox (knowledge bee psi))))) u) ->
    ((vee
      (supset
        (knowledge ei (knowledge xbox (knowledge ei phi)))
        (knowledge ei (knowledge ybox (knowledge bee psi))))
      (supset
        (knowledge bee (knowledge ybox (knowledge bee psi)))
        (knowledge bee (knowledge xbox (knowledge ei phi))))) u).
  intros phi psi u ei bee.
  intro pre.
  apply veeIl.
  apply supsetI.
  intro two.
  apply supsetE with (knowledge ei
    (supset (knowledge xbox (knowledge ei phi))
      (knowledge ybox (knowledge bee psi)))).
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
          (knowledge th0 (knowledge xbox (knowledge th0 phi)))
          (knowledge th0 (knowledge ybox (knowledge th1 psi))))
        (supset
          (knowledge th1 (knowledge ybox (knowledge th1 psi)))
          (knowledge th1 (knowledge xbox (knowledge th0 phi))))) u).
  intros phi psi u.
  apply veeE with 
    (knowledge th1 (knowledge th0 (supset
        (knowledge xbox (knowledge th0 phi))
        (knowledge ybox (knowledge th1 psi)))))
    (knowledge th1 (knowledge th0 (supset
        (knowledge ybox (knowledge th1 psi))
        (knowledge xbox (knowledge th0 phi))))).
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
    (knowledge ybox (knowledge th1 psi))
    (knowledge xbox (knowledge th0 phi)))).
  apply Aright2.
  exact two.
  apply kI1 with (knowledge th0
                (supset (knowledge ybox (knowledge th1 psi))
                   (knowledge xbox (knowledge th0 phi)))).
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
          (knowledge th0 (knowledge xbox (knowledge th0 phi)))
          (knowledge th1 (knowledge ybox (knowledge th1 psi))))
        (vee
          (knowledge th0 (knowledge th1 psi))
          (knowledge th1 (knowledge th0 phi)))) u).
  intros phi psi u.
  apply supsetI.
  intro pre.
apply veeE with 
  (supset
    (knowledge th0 (knowledge xbox (knowledge th0 phi)))
    (knowledge th0 (knowledge ybox (knowledge th1 psi))))
  (supset
    (knowledge th1 (knowledge ybox (knowledge th1 psi)))
    (knowledge th1 (knowledge xbox (knowledge th0 phi)))).
apply B.
intro two.
apply veeIl.
apply C with phi xbox ybox.
exact two.
exact pre.
intro two.
apply veeIr.
apply C with psi ybox xbox.
exact two.
apply wedgeI.
apply wedgeEr with (knowledge th0 (knowledge xbox (knowledge th0 phi))).
exact pre.
apply wedgeEl with (knowledge th1 (knowledge ybox (knowledge th1 psi))).
exact pre.
Defined.

(* extraction of fig2 yields () *)

Axiom write0:
  forall (psi: o) (u: U),
  (knowledge th0 psi) u->
   (knowledge th0 (knowledge xbox (knowledge th0 psi))) u.

Section write0preserve.
  Variable psi : o.
  Variable u : U.
  Variable x: (knowledge th0 psi) u.
  Let saved : (knowledge th0 (knowledge xbox (knowledge th0 psi))) u.
  apply write0.
  exact x.
  Defined.
  Let taken: psi u.
  apply kE with th0.
  exact x.
  Defined.
  Let taken': psi u.
  apply kE with th0.
  apply kE with xbox.
  apply kE with th0.
  exact saved.
  Defined.
  Axiom write0preserve: taken' = taken.
  Hint Resolve write0preserve.
End write0preserve.

Axiom write1:
  forall (psi: o) (u: U),
     (knowledge th1 psi) u ->
     (knowledge th1 (knowledge ybox (knowledge th1 psi))) u.

Section write1preserve.
  Variable psi : o.
  Variable u : U.
  Variable x: (knowledge th1 psi) u.
  Let saved : (knowledge th1 (knowledge ybox (knowledge th1 psi))) u.
  apply write1.
  exact x.
  Defined.
  Let taken: psi u.
  apply kE with th1.
  exact x.
  Defined.
  Let taken': psi u.
  apply kE with th1.
  apply kE with ybox.
  apply kE with th1.
  exact saved.
  Defined.
  Axiom write1preserve: taken' = taken.
  Hint Resolve write1preserve.
End write1preserve.

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
          (knowledge th0 (knowledge xbox (knowledge th0 phi)))
          (knowledge th1 (knowledge ybox (knowledge th1 psi)))).
  apply fig2.
  apply wedgeI.
  apply write0.
  exact one.
  apply write1.
  exact two.
  intro pre.
  apply veeIl.
  apply kI1 with (knowledge th1 psi).
  exact pre.
  intro v.
  intro gamma.
  apply kE with th1.
  apply kE with th0.
  apply gamma.
  intro pre.
  apply veeIr.
  apply kI1 with (knowledge th0 phi).
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
Check kI1 (embed nat) (embed nat) current th0.
Check kI1 (embed nat) (embed nat) current th0 ask_user0.

Section remote_calc.
  Parameter f: nat->nat.
  Check kI1 (embed nat) (embed nat) current th0 ask_user0.
End remote_calc.

(* make calc0 not parameter, but a defined object *)

Definition ioplus: io nat -> io nat -> io nat.
intros x y.
apply bind with nat.
exact x.
clear x.
intro x.
apply bind with nat.
exact y.
clear y.
intro y.
apply ret.
exact (x + y).
Defined.

Lemma add0: owned th0 -> (owned th0) -> (owned th0).
  intros one two.
  apply kI2 with (embed nat) (embed nat).
  exact one.
  exact two.
  clear one two.
  intro v.
  intro within.
  elim within.
  clear within.
  intro knowledge0.
  intro kn.
  elim kn.
  clear kn.
  intro knowledge1.
  intro rest.
  clear rest.
  apply kE in knowledge0.
  apply kE in knowledge1.
  exact (ioplus knowledge0 knowledge1).
Defined.

Lemma add1: owned th1 -> (owned th1) -> (owned th1).
  intros one two.
  apply kI2 with (embed nat) (embed nat).
  exact one.
  exact two.
  intro v.
  intro within.
  elim within.
  clear within.
  intro knowledge0.
  intro rest.
  elim rest.
  clear rest.
  intro knowledge1.
  intro rest.
  clear rest.
  apply kE in knowledge0.
  apply kE in knowledge1.
  exact (ioplus knowledge0 knowledge1).
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
    compute [ex motto_comm more_comm disj_current comm veeE veeIl veeIr supsetE supsetI wedgeEl wedgeEr wedgeI fig2].
    case (B (embed nat) (embed nat) current).
    compute.
    intro pre.
    
    auto.
    intro k.
    


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
    look n = ioplus (look0 ask_user0) (look1 ask_user1)).
  exists (add_own exchanged).
  compute [look].
  compute [look0 look1].
  compute [add_own exchanged].
  compute [motto_comm].
  compute [more_comm].
  compute [disj_current].
  compute [comm].
  compute -[plus].
Abort All.

End changed.

