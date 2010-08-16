Require Import FSets.


Module NS := FSetList.Make (Nat_as_DT).
Import NS.
Module NSProp := WProperties_fun (Nat_as_DT)(NS).
Import NSProp.

Section model.

  (* input domain for each process *)
  Variable I: Set.

  (* processes, should be finite *)

  Variable P: NS.t.

  (* local states for each process *)
  Variable S: Set.
  Variable boringS: S.

  (* type of values written to and read from a register *)
  Variable  V: Set.
  Require Import List.
  Definition Vs := list V.
  Definition boringVs : Vs.
  exact nil.
  Defined.

  (* initial state *)
  Definition E:= nat -> S.

  (* written value *)
  Definition W:= S -> V.

  (* reading and computing *)
  Definition U:= S -> (nat -> Vs) -> S.

  (* protocol *)
  Open Local Scope type_scope.
  Definition Protocol := S * V * E * W * U.

  (* state configuration *)
  Definition SysConf := (nat -> S) * (nat ->Vs).

  Definition is_block (b: NS.t) :=
    (NS.Subset b P) /\ ~ (NS.Empty b).

  Definition update: Protocol -> SysConf -> NS.t -> SysConf.
  intro protocol.
  intro initial.
  intro b.
  split.
  intro p.
  generalize (NS.mem p P).
  intro process.
  generalize (NS.mem p b).
  intro member.
  induction protocol as [protocol u].
  induction initial as [initialS initialM].
  exact (
    match process with
      | false => boringS
      | true  =>
        (match member with
           | true => (u (initialS p) initialM)
           | false => initialS p
         end)
    end).
  intro address.
  generalize (NS.mem address P).
  intro in_range.
  generalize (NS.mem address b).
  intro updated.
  induction protocol as [protocol u].
  clear u.
  induction protocol as [protocol w].
  clear protocol.
  induction initial as [initialS initialM].
  exact (
    match in_range with
      | false => boringVs
      | true =>
        match updated with
          | false => initialM address
          | true => cons (w (initialS address)) (initialM address)
        end
    end).
  Defined.

(* Now, let's read the coinduction part of the Coq'Art book *)
  Require Import Streams.
  Definition ScheduleT := Stream NS.t.
  CoInductive IsSchedule (s: ScheduleT) :Prop:=
    isschedule:
    is_block (hd s) -> IsSchedule (tl s) -> IsSchedule s.
  CoInductive Sigma (b: NS.t) (s: ScheduleT): Prop :=
    sigma:
    Sigma b (tl s) -> (NS.Subset (hd s) b) -> Sigma b s.
  Inductive Active (s: ScheduleT) (p :nat) : Prop :=
    | here: (NS.In p (hd s)) -> Active s p
    | later: Active (tl s) p -> Active s p.
(* I don't know whether these definitions are used later, but still *)
  CoInductive Inactive (s: ScheduleT) (p: nat) : Prop :=
    inactive:
Inactive (tl s) p -> ~(NS.In p (hd s)) -> Inactive s p.
CoInductive NonFaulty (s: ScheduleT) (p: nat) : Prop :=
  nonfaulty:
  Active s p -> NonFaulty (tl s) p -> NonFaulty s p.
Inductive Faulty (s: ScheduleT) (p: nat) : Prop :=
  | nolater: Inactive s p -> Faulty s p
  | sometime: Faulty (tl s) p -> Faulty s p.

Lemma observe: forall (b: NS.t) (s: ScheduleT),
  IsSchedule s ->
  (Sigma b s <-> (forall p:nat, Active s p -> (NS.In p b))).
intros b s.
intro sch.
split.
intro sig.
intro p.
intro act.
induction act.
apply in_subset with (hd s).
exact H.
case sig.
intros one two.
exact two.
apply IHact.
clear IHact.
case sch.
intro irr.
trivial.
case sig.
intros one two.
exact one.
generalize sch.
generalize s.
clear s sch.
clear boringS S I.
cofix.
intros s sch pre.
apply sigma.
apply observe.
case sch.
intros irr.
clear irr.
intro lsch.
exact lsch.
intros p tlpre.
apply pre.
apply later.
exact tlpre.
compute [Subset].
intro p.
intro inhead.
assert (Active s p).
apply here.
exact inhead.
apply pre.
exact H.
Qed.






