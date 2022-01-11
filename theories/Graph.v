Require Import Dep.Syntax.

Require Import Lists.List.
From mathcomp Require Import all_ssreflect.
From Equations Require Import Equations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Program. 
Require Import Lia.

Ltac uf name := rewrite /name -/name.

Section Enumeration.
Variable U : countType.
Implicit Type g : gType U.
Fixpoint gType_size g :=
match g with
 | GMsg a u g0 => 1 + (gType_size  g0)
 | GRec g0 => 1 + (gType_size g0)
 | GBranch a gs => 1 + (sumn (map gType_size gs))
 | GEnd => 1
(* | GPar g0 g1 => 1 + (gType_size g0) + (gType_size g1)*)
 | GVar n => 1
end.

Fixpoint mu_height g :=
match g with
| GRec g0 => (mu_height g0).+1
| _ => 0
end.

Fixpoint unf_recs_aux n g  :=
if n is n'.+1 then
  if g is GRec g' then unf_recs_aux n' (g'[g])
  else g
else g.

Notation unf_recs g := (unf_recs_aux (mu_height g) g).


Lemma contractive_mu_height : forall (g0 g1 : gType U) i, contractive_i (S i) g0 -> mu_height (substitution i g0 g1) = mu_height g0.
Proof. 
elim; try solve [by rewrite /=].
- rewrite /=. intros. case : (eqVneq n i) H. move=>->. by rewrite ltnn. by rewrite /=. 
- intros. rewrite /=. f_equal. apply H. done. 
Qed.


Lemma bound_lt : forall (g : gType U) i j, i < j -> bound_i i g -> bound_i j g.
Proof. 
elim/gType_ind_list.
- rewrite /=;auto. move=>n i j.  move=> /leP H /ltP H1. apply/ltP.  lia. 
- rewrite /=;auto. intros. apply : (@H i.+1 j.+1); done. 
- rewrite /=;auto. 
- intros. move : H1. rewrite /=.  move/allP=>H2. apply/allP. move=> l' Hin. move : (H2 l' Hin). 
  apply H;auto. 
- intros. simpl in H. done.
- rewrite /=. intros. case : H1 H3. rewrite inE. case/orP. move/eqP=>->. eauto. 
  eauto.
Qed.


Lemma bound_0 : forall (g : gType U) j, bound g -> bound_i j g.
Proof.
intros. case : j. done. intros. apply  : (@bound_lt _ 0). done. done.
Qed.

Lemma bound_subst : forall (g g': gType U) i, bound_i (S i) g -> bound g' -> bound_i i (substitution i g g').
Proof.
elim/gType_ind_list.
-  rewrite /=;intros;case : (eqVneq n i).
   move=><-. apply bound_0. done. rewrite /bound_i. move : H. move=> /ltP H1 /eqP H2. 
   apply/ltP. lia. 
- rewrite /=. done. 
- rewrite /=. intros. apply H. done. done.
- rewrite /=. intros. auto. 
- rewrite /=. intros. move : (allP H0)=> H2. apply/allP. move => l' /mapP. case. intros. 
  subst. apply H;auto.
- rewrite /=. move => g. by rewrite in_nil. 
- move => g H l IH g0. rewrite inE. case/orP. move/eqP =>->; auto. auto. 
Qed.

Lemma contractive_lt : forall (g : gType U) i j, j < i -> contractive_i i g -> contractive_i j g.
Proof.
elim;auto.
- rewrite /=. move => n i j. move/ltP=> + /leP;intros.  apply/leP. lia. 
- move => g H.  rewrite /=. intros. have : j.+1 < i.+1. apply/ltP. move : H0. move/ltP. lia. eauto. 
Qed.

Lemma contractive_0 : forall (g : gType U) i,  contractive_i i g -> contractive g.
Proof.
move=> g. case. done. intros.  apply : contractive_lt; last eauto. done.
Qed.

Lemma bound_contractive_subst : forall (g g': gType U) i j, bound_i (S i) g -> contractive_i j g -> bound g' -> (forall j, contractive_i j g') -> 
contractive_i j (substitution i g g').
Proof.
elim/gType_ind_list; (try solve [rewrite /= ;auto]).
- rewrite/=. move => v g' i j. case : (eqVneq v i).  done. simpl. done.
- rewrite /=. intros. apply/allP. move=> gsub /mapP. case. intros. subst. 
  apply H;auto. auto using (allP H0), (allP H1). auto using (allP H1). 
- rewrite /=. intros.  move : H1 H2 H3. rewrite inE. case/orP. move/eqP=>->. 
  eauto. eauto. 
Qed.

Lemma bound_cont_eq : forall (g : gType U) i, bound_i i g -> contractive_i i g -> (forall j, contractive_i j g).
Proof.
elim; rewrite/=;auto.
- rewrite /=. move => v i /ltP + /leP. lia. 
- rewrite /=. intros. eauto. 
Qed.

Lemma unf_recs_helper : forall n g, bound g -> contractive g -> mu_height (unf_recs_aux n g) = (mu_height g) - n.
Proof.
elim. 
- intros. rewrite /=. Search _ (_ - _). elim : (mu_height g);done. 
- intros. rewrite /=. case : g H0 H1; rewrite /= //=.
intros. rewrite subSS. rewrite H. rewrite contractive_mu_height //=.
- auto using bound_subst. 
- apply bound_contractive_subst;auto. apply : contractive_0. eauto.  apply : bound_cont_eq. 
 eauto. rewrite /=. done. 
Qed.

(*unf_recs unfolds all mu's, if g is bound and contractive, this is only relevant
 for the specification of linearity
 We trust that act_of_g and g_next do as intended*)
Lemma unf_recs_fully : forall g, bound g -> contractive g -> mu_height (unf_recs g) = 0. 
Proof. 
intros. rewrite unf_recs_helper //=. rewrite subnE /=.
remember (mu_height g). clear Heqn. elim : n. done. done. 
Qed.

Definition act_of_g g :=
match unf_recs g with 
| GMsg a _ _ => Some a
| GBranch a _ => Some a
| _ => None
end.

Definition g_next g :=
match unf_recs g with 
| GMsg _ _ g0 => [::g0]
| GBranch _ gs => gs
| _ => [::]
end.

Fixpoint gType_enum_aux n gs g :=
if n is n'.+1 then
  if g \in gs then gs
   else foldl (gType_enum_aux n') (g::gs) (g_next g)
else gs.

Definition gType_enum (g : gType U) := undup (filter (fun g_f : gType U => act_of_g g_f != None) (gType_enum_aux (gType_size g) nil g)).
End Enumeration.
Arguments g_next {_}.
Arguments gType_enum {_}.

Section Node.
Variable U : countType.
Variable g : gType U.

Inductive node := Node (g_n : gType U) of g_n \in gType_enum g. 

Definition node_project (n : node) : gType U := let: Node p _ := n in p. 
Canonical node_subType := [subType for node_project]. 
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

Lemma in_undup : forall (A : eqType) (l : seq A) (a : A), a \in (undup l) -> a \in l.
Proof. 
move => A. elim. 
- by rewrite /=.
- move => a l IH a0.  rewrite /=. case: (@idP (a \in l)). 
 + intros. rewrite /=. rewrite inE. case : (eqVneq a0 a). done. 
   rewrite /=. auto. 
 + move => H. rewrite inE. case/orP. move/eqP=>->. by rewrite inE eqxx.
  move/IH. rewrite inE. move=>->. apply/orP;auto. 
Qed.

Lemma action_exists : forall n, { a : action | act_of_g (node_project n) = Some a }.
Proof. 
elim. rewrite /gType_enum. move => gn i. move : (in_undup i). rewrite mem_filter. move/andP. case. 
intros. destruct (act_of_g gn) eqn:Heqn. eauto.  done. 
Qed.

Definition act_of_n (n : node) := let: exist a _ := action_exists n in a. 

Definition node_finMixin := Eval hnf in UniqFinMixin node_enum_uniq mem_node_enum.
Canonical node_finType := Eval hnf in FinType node node_finMixin.
Canonical node_subFinType := Eval hnf in [subFinType of node].
End Node.
Arguments Node {_}.
Arguments gType_enum {_}.
Coercion act_of_n : node >-> action. 
Coercion node_project : node >-> gType.

Section Order.
Variable (U : countType). 
Variable (g : gType U).

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

Definition II_aux (a0 a1 : action) := (action_to a0 == action_to a1).
Definition II (n0 n1 : node g) := (grel g_next n0 n1) && II_aux n0 n1.
Definition II_spec (g0 g1 : gType U) := (grel g_next g0 g1) && opt_rel g0 g1 II_aux. 

Definition IO_aux (a0 a1 : action) := (action_to a0 == action_from a1).
Definition IO (n0 n1 : node g) := (grel g_next n0 n1) && IO_aux n0 n1.
Definition IO_spec (g0 g1 : gType U) := (grel g_next g0 g1) && opt_rel g0 g1 IO_aux. 

Definition OO_aux (a0 a1 : action) := (action_from a0 == action_from a1) && (action_ch a0 == action_ch a1).
Definition OO (n0 n1 : node g) := (grel g_next n0 n1) && OO_aux n0 n1.
Definition OO_spec (g0 g1 : gType U) := (grel g_next g0 g1) && opt_rel g0 g1 OO_aux. 

Definition in_dep (n0 n1 : node g) := [exists n', connect IO n0 n' && II n' n1] || II n0 n1. 
Definition in_dep_spec (g0 g1 : gType U) := (exists (g' : gType U), (exists2 p, path IO_spec g0 p & g' = last g0 p) /\ II_spec g' g1) 
                                      \/ II_spec g0 g1.


Definition OO_IO (n n' : node g) := OO n n' || IO n n'.
Definition OO_IO_spec (g g' : gType U) := OO_spec g g' || IO_spec g g'.
Definition out_dep (n0 n1 : node g) := connect OO_IO n0 n1. 
Definition out_dep_spec(g0 g1 : gType U) := exists2 p, path OO_IO_spec g0 p & g1 = last g0 p.

Definition adjacent_rel (n0 n1 : node g) := (grel g_next) n0 n1.
Definition linear := [forall n0 : node g, forall (n1 : node g | connect adjacent_rel n0 n1 && same_ch n0 n1), in_dep n0 n1 && out_dep n0 n1].
Definition linear_spec := 
forall (g0 g1 : gType U), (exists2 p, path (grel g_next) g p & g0 = last g p) ->
                     (exists2 p, path (grel g_next) g0 p & g1 = last g0 p) ->
  opt_rel g0 g1 same_ch -> bound g -> contractive g -> in_dep_spec g0 g1 /\ out_dep_spec g0 g1.

Lemma linearP : reflect linear_spec linear.
Proof. Admitted.
End Order. 
