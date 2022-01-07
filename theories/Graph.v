Require Import Dep.Syntax.

Require Import Lists.List.
From mathcomp Require Import all_ssreflect.
From Equations Require Import Equations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Program. 
Require Import Lia.

Fixpoint unfold_top_recs_aux (U : countType) (n : nat) (g : gType U) :=
if n is n'.+1 then
  if g is GRec g' then unfold_top_recs_aux n' (g'[g])
  else g
else g.

Fixpoint mu_height (U : countType) (g : gType U) :=
match g with
| GRec g0 => 1 + (mu_height g0)
| _ => 0
end.

Definition unfold_top_recs (U : countType) (g : gType U) := 
 unfold_top_recs_aux (mu_height g) g.


Section AGType.
Variable (U : countType).
Definition act_of_gType (g : gType U) :=
match (unfold_top_recs g) with 
| GMsg a _ _ => Some a
| GBranch a _ => Some a
| _ => None
end.

Definition has_prefix (g : gType U) := act_of_gType g != None.

Inductive agType := AGType g of has_prefix g.

Definition agType_project ag := let: AGType g _ := ag in g.
Canonical agType_subType := [subType for agType_project]. 
Definition agType_eqMixin := Eval hnf in [eqMixin of agType by <:].
Canonical agType_eqType := Eval hnf in EqType agType agType_eqMixin.
Definition agType_choiceMixin := [choiceMixin of agType by <:].
Canonical agType_choiceType :=
  Eval hnf in ChoiceType agType agType_choiceMixin.
Definition agType_countMixin := [countMixin of agType by <:].
Canonical agType_countType := Eval hnf in CountType agType agType_countMixin.
Canonical agType_subCountType := [subCountType of agType].

Lemma action_exists : forall (ag : agType), { a : action | act_of_gType (agType_project ag) = Some a }.
Proof. Admitted.

Definition action_of_ag (ag : agType) := let: exist a _ := action_exists ag in a.


End AGType.
Check agType.
Definition gType_of_agType : forall (U : countType), agType U -> gType U := agType_project.
Coercion gType_of_agType : agType >-> gType.
Definition action_of_agType : forall (U : countType), agType U -> action := action_of_ag.
Coercion action_of_ag : agType >-> action.


Section Graph.
Variable (U : countType). 
Check foldl.

Definition g_next (g : gType U) : seq (gType U) :=
match g with 
| GMsg _ _ g0 => [::g0]
| GBranch _ gs => gs
| GPar g0 g1 => [::g0;g1]
| GRec g0 => [::unfold_top_recs g0]
| _ => [::]
end.

Definition ag_next (ag : agType U) : seq (agType U) := 
 pmap insub (g_next ag).

Fixpoint agType_enum_aux (n : nat) (ags : seq (agType U)) (ag : agType U) : seq (agType U) :=
if n is n'.+1 then
  if ag \in ags then ags
   else foldl (agType_enum_aux n') (ag::ags) (ag_next ag)
else ags.

Fixpoint gType_size (g : gType U) :=
match g with
 | GMsg a u g0 => 1 + (gType_size g0)
 | GRec g0 => 1 + (gType_size g0)
 | GBranch a gs => 1 + (sumn (map gType_size gs))
 | GEnd => 1
 | GPar g0 g1 => 1 + (gType_size g0) + (gType_size g1)
 | GVar n => 1
end. 

Definition agType_enum (ag : agType U) := agType_enum_aux (gType_size ag) ([::]) ag.

Section Node.
Variable ag : agType U.

Inductive node := Node ag_n of ag_n \in (agType_enum ag).

Definition node_project n := let: Node ag_n _ := n in ag_n.
Canonical node_subType := [subType for node_project]. 
Definition node_eqMixin := Eval hnf in [eqMixin of node by <:].
Canonical node_eqType := Eval hnf in EqType node node_eqMixin.
Definition node_choiceMixin := [choiceMixin of node by <:].
Canonical node_choiceType :=
  Eval hnf in ChoiceType node node_choiceMixin.
Definition node_countMixin := [countMixin of node by <:].
Canonical node_countType := Eval hnf in CountType node node_countMixin.
Canonical node_subCountType := [subCountType of node].

Definition node_next (n : node) : seq node := 
 pmap insub (ag_next (node_project n)).

Lemma in_node (n : node) : (node_project n) \in (agType_enum ag).
Proof. Admitted.

(*Lemma node_inj : injective node_project. 
Proof. Admitted.*)

Definition node_enum : seq node := pmap insub (agType_enum ag).

Lemma node_enum_uniq : uniq node_enum.
Proof. Admitted.

Lemma mem_node_enum n : n \in node_enum.
Proof. Admitted.


Definition node_finMixin := Eval hnf in UniqFinMixin node_enum_uniq mem_node_enum.
Canonical node_finType := Eval hnf in FinType node node_finMixin.
Canonical node_subFinType := Eval hnf in [subFinType of node].

End Node.
End Graph.
Arguments Node {_}.
Check node_next.
Arguments node_next {_} {_}.

Definition agType_of_node : forall (U : countType) (g : agType U), node g -> agType U := node_project.
Coercion agType_of_node : node >-> agType.

Section Order.
Variable (U : countType). 

Definition action_from (a : action) := let : Action p0 _ _ := a in p0.
Definition action_to (a : action) := let : Action _ p1 _ := a in p1.
Definition action_ch (a : action) := let : Action _ _ c := a in c.

Variable (ag : agType U).

Definition II_rel (n0 n1 : node ag) := (action_to n0 == action_to n1).
Definition IO_rel (n0 n1 : node ag) := (action_to n0 == action_from n1).
Definition OO_rel (n0 n1 : node ag) := (action_from n0 == action_from n1) && (action_ch n0 == action_ch n1).

Definition in_dep (n0 n1 : node ag) := [exists n', connect IO_rel n0 n' && II_rel n' n1] || II_rel n0 n1.
Definition out_dep (n0 n1 : node ag) := connect (fun n0 n1 => OO_rel n0 n1 || IO_rel n0 n1) n0 n1.
End Order.
Arguments in_dep {_} {_}.
Arguments out_dep {_} {_}.

Section Linear.
Variable (U : countType).


Definition linear (g : gType U) := 
if insub g is Some ag then [forall n0 : node ag, forall (n1 : node ag | action_ch n0 == action_ch n1), in_dep n0 n1 && out_dep n0 n1]
                      else true.

