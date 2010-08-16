Require Import FSets.


Module NS := FSetList.Make (Nat_as_DT).
Import NS.
Module NSProp := WProperties_fun (Nat_as_DT)(NS).
Import NSProp.

Section model.

  (* input domain for each process *)
  Variable I: Set.
  Variable boringI: I.

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
  Definition eType := I -> nat -> S.

  (* written value *)
  Definition W:= S -> V.

  (* reading and computing *)
  Definition U:= S -> (nat -> Vs) -> S.

  (* protocol *)
  Open Local Scope type_scope.
  Definition Protocol := eType * W * U.

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
  
  Definition ScheduleT := Stream (NS.t * NS.t).
  (* the second element of the tuple shows the set of active processes *)

  CoInductive Sigma (b: NS.t) (s: ScheduleT): Prop :=
    sigma:
    Sigma b (tl s) -> (NS.Subset (fst (hd s)) b) -> Sigma b s.
  Inductive Active (s: ScheduleT) (p :nat) : Prop :=
    | here: (NS.In p (fst (hd s))) -> Active s p
    | later: Active (tl s) p -> Active s p.
(* I don't know whether these definitions are used later, but still *)

  CoInductive IsSchedule (s: ScheduleT) :Prop:=
    isschedule:
    is_block (fst (hd s)) ->
    (forall p:nat,
      Active s p <-> NS.In p (snd (hd s)))
    -> IsSchedule (tl s) -> IsSchedule s.

  CoInductive Inactive (s: ScheduleT) (p: nat) : Prop :=
    inactive:
Inactive (tl s) p -> ~(NS.In p (fst (hd s))) -> Inactive s p.
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
apply in_subset with (fst (hd s)).
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
clear boringS S boringI I.
cofix.
intros s sch pre.
apply sigma.
apply observe.
case sch.
intros irr.
clear irr.
intro no.
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

Definition FragmentT := list NS.t.

Fixpoint Phi (b: NS.t) (s: FragmentT): Prop :=
match s with
| nil => True
| cons h ta => NS.Subset b h /\  Phi b ta
end.

Fixpoint ActiveF (s: FragmentT) (p: nat) : Prop :=
match s with
| nil => False
| cons h ta => NS.In p h \/  ActiveF ta p
end.

Fixpoint InactiveF (s: FragmentT) (p: nat) : Prop :=
match s with
| nil => True
| cons h ta => ~ (NS.In p h) /\  ActiveF ta p
end.

Fixpoint NS_from_Fragment (s: FragmentT) : NS.t :=
  match s with
    | nil => empty
    | cons hd tal => NS.union hd (NS_from_Fragment tal)
  end.

Definition extend_active (t:ScheduleT) (s: FragmentT) :=
  match t with
    Cons (_, tactive) _ =>
    union tactive (NS_from_Fragment s)
  end.

Fixpoint extension (s: FragmentT) (t: ScheduleT): ScheduleT :=
  match s with
    | nil => t
    | cons h ta => Cons (h, extend_active t s) (extension ta t)
  end.

Fixpoint is_prefix (s: FragmentT) (t: ScheduleT): Prop :=
  match s with
    | nil => True
    | cons sh sl =>
      match t with
        Cons th tll => sh = th /\ is_prefix sl tll
      end
  end.


Notation "'[' J ']'" := (const J).

Notation "'[[' p ']]'" := (const (singleton p)).

Definition RunT := Protocol * (nat -> I) * ScheduleT.

Definition is_run (r: RunT): Prop.
intro r.
destruct r.
exact (IsSchedule s).
Defined.
        
Definition PartialRunT := Protocol * (nat -> I) * FragmentT.

Print ScheduleT.

CoFixpoint E_inner (r: RunT) (C: SysConf) : Stream SysConf :=
  match r with
    ((p, init), Cons sch scl) =>
    Cons C (E_inner r (update p C sch))
  end.

Definition InitialConf: RunT -> SysConf.
intro run.
destruct run as [protocol _].
destruct protocol as [protocol init].
destruct protocol as [protocol _].
destruct protocol as [e _].
split.
intro procid.
exact (
  if NS.mem procid P
    then
      (e (init procid) procid)
    else 
      boringS).
intro address.
exact nil.
Defined.

Definition E (r:RunT) := E_inner r (InitialConf r).

(* define E for PartialRun *)

(* reading later:
   now thinking how epistemic logic applies *)

(* public record is may be finite as well as infinite *)

CoInductive Vhis :Set :=
  | HNil
  | HCons: V -> Vhis -> Vhis.

CoFixpoint Pub_inner (procid: nat) (s: Stream SysConf) :=
  match s with
    Cons conf later =>
    

Section computation.

Variable D: Set.



End computation.







Definition formula_sem :=
  

Definition Atom := (nat -> I) -> D -> Prop.

(* input -> output -> is_it_success? *)

(* I_a 
no semantics:

I_a : (nat -> I) -> I -> Prop :=
  init a = b

*)

(* S can be set by the protocol *)

(*
K_a I_a: (nat -> I) -> (list nat) * I -> Prop :=

b = ([a], init a) <- this should be a signature-like something...

外側で与えるしかないのかもしれない．
たとえば，update関数を変更して，署名型にしてしまったりとか．


forall (sign: nat -> Set -> Set),
 will be useful in the same way as ST schedule.
   *)

(* what about wedge, supset?? *)

(* wedge ,
   original (O0, R0)  (O1, R1) ->
   (O0 * O1, left -> R0, right -> R1)
*)

(* supset,
   original (O0, R0) (O1, R1) ->
   Km p -> Km q or Km p -> Kmq

   this can be deduced from schedule.

   Ka p -> Kb q || Kb q -> Ka p
   is not available in general?

   this disjunction seems deducible from schedule.

   yes. Every Ka is behind Km thus this is OK.
*)


(*
   difficulty:
   what is the meaning for
   p q r s |- t ?
*)


Definition realize (p:protocol) (a:Atom) :=
  forall i:(nat->I) s:schedule
    reoijojo.