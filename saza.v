Require Import FSets.

Module NatSet := FSetList.Make (Nat_as_OT).

Section model.

  (* input domain for each process *)
  Variable I: Set.

  (* processes, should be finite *)

  Variable P: NatSet.t.

  (* local states for each process *)
  Variable S: Set.
  Variable boringS: S.

  (* type of values written to and read from a register *)
  Variable  V: Set.
  Require Import List.
  Definition Vs := list V.
  Definition boringVs : Vs.
  exact (nil).
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

  Require Import Bool.
  Definition is_block (b: NatSet.t) :=
    Is_true (NatSet.subset b P) /\ ~ (Is_true (NatSet.is_empty b)).

  Definition update: Protocol -> SysConf -> NatSet.t -> SysConf.
  intro protocol.
  intro initial.
  intro b.
  split.
  intro p.
  generalize (NatSet.mem p P).
  intro process.
  generalize (NatSet.mem p b).
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
  generalize (NatSet.mem address P).
  intro in_range.
  generalize (NatSet.mem address b).
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

