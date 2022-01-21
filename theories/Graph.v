Require Import Dep.Syntax.

Require Import Lists.List.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import zify.
From mathcomp Require Import finmap.
From Equations Require Import Equations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Program. 

(*Much in this file is not necessary. We need an enumeration, its cartesian product, a filter of the action prefixed values and then the in_dep and out_dep relations
  fingraph is not needed, so scratch the rest*)

Section Node.
Variable U : countType.
Variable g : gType U.

Inductive node := Node (g_n : gType U) of g_n \in gType_enum g. 

Definition g_of_n (n : node) : gType U := let: Node p _ := n in p. 
Canonical node_subType := [subType for g_of_n]. 
Definition node_eqMixin := Eval hnf in [eqMixin of node by <:].
Canonical node_eqType := Eval hnf in EqType node node_eqMixin.
Definition node_choiceMixin := [choiceMixin of node by <:].
Canonical node_choiceType :=
  Eval hnf in ChoiceType node node_choiceMixin.
Definition node_countMixin := [countMixin of node by <:].
Canonical node_countType := Eval hnf in CountType node node_countMixin.
Canonical node_subCountType := [subCountType of node].

Definition node_enum : seq node := pmap insub (gType_enum g).

Lemma mem_node_enum n : n \in node_enum.
Proof. rewrite /node_enum. rewrite mem_pmap_sub. 
case : n. intros. rewrite /=. done. 
Qed.

Lemma node_enum_uniq : uniq node_enum.
Proof. rewrite pmap_sub_uniq //=. 
rewrite /gType_enum. apply undup_uniq. 
Qed.


Lemma action_exists : forall n, { a : action | act_of_g (g_of_n n) = Some a }.
Proof. 
elim. rewrite /gType_enum. move => gn i. destruct (act_of_g gn) eqn:Heqn. exists a. 
rewrite /=. rewrite Heqn. done. exfalso. move : i. by rewrite mem_undup mem_filter Heqn /=.
Qed.

Definition act_of_n (n : node) := let: exist a _ := action_exists n in a. 

Definition node_finMixin := Eval hnf in UniqFinMixin node_enum_uniq mem_node_enum.
Canonical node_finType := Eval hnf in FinType node node_finMixin.
Canonical node_subFinType := Eval hnf in [subFinType of node].
End Node.
Arguments Node {_}.
Arguments gType_enum {_}.
Arguments g_of_n {_} {_}. 
Coercion act_of_n : node >-> action. 
Coercion g_of_n : node >-> gType.


Section Linearity.
Variable (U : countType). 
Variable (g : gType U).
Hypotheses (Hbound : bound g) (Hcont : contractive g).

Definition action_from (a : action) := let : Action p0 _ _ := a in p0.
Definition action_to (a : action) := let : Action _ p1 _ := a in p1.
Definition action_ch (a : action) := let : Action _ _ c := a in c.
Definition same_ch (a0 a1 : action) := action_ch a0 == action_ch a1.

Definition opt_rel (g0 g1 : gType U) (P : rel action) :=
if act_of_g g0 is Some a0
  then if act_of_g g1 is Some a1
    then P a0 a1
  else false 
else false.

Lemma act_of_g_of_n : forall (n : node g), act_of_g (g_of_n n) = Some (act_of_n n).
Proof.
case. intros. rewrite /=. rewrite /act_of_n. 
case : (action_exists (Node g g_n i)). rewrite /=. done.  
Qed.


Lemma opt_relP (n0 n1 : node g) (P : rel action) : reflect (P n0 n1) (opt_rel n0 n1 P).
Proof. rewrite /opt_rel.  rewrite !act_of_g_of_n. apply idP. 
Qed.


Definition II_aux (a0 a1 : action) := (action_to a0 == action_to a1).
Definition II (n0 n1 : node g) := (grel g_next n0 n1) && II_aux n0 n1.
Definition II_spec (g0 g1 : gType U) := (grel g_next g0 g1) && opt_rel g0 g1 II_aux. 

Lemma IIP (n0 n1 : node g) : reflect (II_spec n0 n1) (II n0 n1).
Proof. 
rewrite /II /II_spec. apply Bool.iff_reflect. split;
 move/andP=>[H0 H1]; apply/andP; split;auto; apply/opt_relP; done.
Qed.

Definition IO_aux (a0 a1 : action) := (action_to a0 == action_from a1).
Definition IO (n0 n1 : node g) := (grel g_next n0 n1) && IO_aux n0 n1.
Definition IO_spec (g0 g1 : gType U) := (grel g_next g0 g1) && opt_rel g0 g1 IO_aux. 
Lemma IOP (n0 n1 : node g) : reflect (IO_spec n0 n1) (IO n0 n1).
Proof. 
rewrite /IO /IO_spec. apply Bool.iff_reflect. split;
 move/andP=>[H0 H1]; apply/andP; split;auto; apply/opt_relP; done.
Qed.

Definition OO_aux (a0 a1 : action) := (action_from a0 == action_from a1) && (action_ch a0 == action_ch a1).
Definition OO (n0 n1 : node g) := (grel g_next n0 n1) && OO_aux n0 n1.
Definition OO_spec (g0 g1 : gType U) := (grel g_next g0 g1) && opt_rel g0 g1 OO_aux. 
Lemma OOP (n0 n1 : node g) : reflect (OO_spec n0 n1) (OO n0 n1).
Proof. 
rewrite /OO /OO_spec. apply Bool.iff_reflect. split;
 move/andP=>[H0 H1]; apply/andP; split;auto; apply/opt_relP; done.
Qed.

Definition in_dep (n0 n1 : node g) := [exists n', connect IO n0 n' && II n' n1] || II n0 n1. 
Definition in_dep_spec (g0 g1 : gType U) := (exists (g' : gType U), (exists2 p, path IO_spec g0 p & g' = last g0 p) /\ II_spec g' g1) 
                                      \/ II_spec g0 g1.

Definition in_dep_spec_aux (n0 n1 : node g) := (exists (n' : node g), (exists2 p : seq (node g), path IO_spec n0 (map g_of_n p) & n' = last n0 p) /\ II_spec n' n1) \/ II_spec n0 n1.

Lemma in_dep_in_dep_spec_aux : forall (n0 n1 : node g), in_dep n0 n1 <-> in_dep_spec_aux n0 n1.
Proof. Admitted.


Lemma in_depP (n0 n1 : node g) : reflect (in_dep_spec n0 n1) (in_dep n0 n1).
Proof. Admitted.


Definition OO_IO (n n' : node g) := OO n n' || IO n n'.
Definition OO_IO_spec (g g' : gType U) := OO_spec g g' || IO_spec g g'.
Definition out_dep (n0 n1 : node g) := connect OO_IO n0 n1. 
Definition out_dep_spec(g0 g1 : gType U) := exists2 p, path OO_IO_spec g0 p & g1 = last g0 p.

(*Definition adjacent_rel (n0 n1 : node g) := (grel g_next) n0 n1.*)
Definition linear := [forall n0 : node g, forall (n1 : node g | connect (grel g_next) n0 n1 && same_ch n0 n1), in_dep n0 n1 && out_dep n0 n1].

Definition linear_spec := 
forall (g0 g1 : gType U), (exists2 p, path (grel g_next) g p & g0 = last g p) ->
                     (exists2 p, path (grel g_next) g p & g1 = last g p) ->
                     (exists2 p, path (grel g_next) g0 p & g1 = last g0 p) ->
                     opt_rel g0 g1 same_ch -> in_dep_spec g0 g1 /\ out_dep_spec g0 g1.

Lemma linearP : reflect linear_spec linear.
Proof.
Admitted.
End Linearity. 

(*define what a race is later*)

(*sanity checks*)


