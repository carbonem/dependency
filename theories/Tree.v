Require Import Dep.Syntax.

Require Import Lists.List.
From mathcomp Require Import all_ssreflect.
From Equations Require Import Equations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Program. 
Require Import Lia.

Section TreeOf.
Variable (U : eqType).

Fixpoint mu_height (g : gType U) :=
match g with
| GRec g0 => 1 + (mu_height g0)
| _ => 0
end.

Notation lexicographic R S := (Subterm.lexprod _ _ R S).

Definition tree_of_ord := (lexicographic lt lt ).

Instance wf_prod : WellFounded tree_of_ord.
Proof.
unfold tree_of_ord. apply Subterm.wellfounded_lexprod; apply  Subterm.lt_wf. 
Qed.

Lemma contractive_mu_height : forall g0 g1 i, contractive_i (S i) g0 -> mu_height (substitution i g0 g1) = mu_height g0.
Proof. 
induction g0; try solve [by rewrite /=].
- rewrite /=. intros. case : (eqVneq v i) H. move=>->. by rewrite ltnn. by rewrite /=. 
- intros. rewrite /=. f_equal. apply IHg0. move : H. by rewrite /=.
Qed.


(*Francisco*)
Lemma InP (A : eqType) (x : A) l : reflect (List.In x l) (x \in l).
Proof.
  elim l; first by apply: ReflectF.
  move=> a {l}l Ih/=; rewrite in_cons; case: eqP=>[->|x_aF].
  + by apply: ReflectT; left.
  + case: Ih=>[x_l|x_lF].
    - by apply: ReflectT; right.
    - by apply: ReflectF=>[[/esym-x_a|x_l]].
Qed.

Lemma bound_lt : forall (g : gType U) i j, i < j -> bound_i i g -> bound_i j g.
Proof. 
elim.
- rewrite /=;auto. move=>n i j.  move=> /leP H /ltP H1. apply/ltP.  lia. 
- rewrite /=;auto. intros. apply : (@H i.+1 j.+1); done. 
- rewrite /=;auto. 
- intros. move : (allP H1) => H2. apply/allP.  move=> Hin H4. apply H2 in H4 as H5. apply : (H _ _ _ _ H0).
  apply/InP.  done. done. 
- rewrite /=.  intros. apply : H. apply : H0. done.
- rewrite /=. intros. move : (andP H2)=>[] H3 H4.  apply/andP. split. apply : H. apply : H1. done.
  apply : H0.  apply H1. done.
Qed.

Lemma bound_0 : forall (g : gType U) j, bound g -> bound_i j g.
Proof.
intros. case : j. done. intros. apply  : (@bound_lt _ 0). done. done.
Qed.

Lemma bound_subst : forall (g g': gType U) i, bound_i (S i) g -> bound g' -> bound_i i (substitution i g g').
Proof.
elim.
- rewrite /=. done. 
-  rewrite /=;intros;case : (eqVneq v i).
   move=><-. apply bound_0. done. rewrite /bound_i. move : H. move=> /ltP H1 /eqP H2. 
   apply/ltP. lia. 
- rewrite /=. intros. apply H. done. done.
- rewrite /=. intros. apply/allP. move=> g Hg. move : (allP H0). simpl in *. move : (mapP Hg).  
  case. intros. subst. apply H. apply/InP. done.  apply elimT. done. done. 
- rewrite /=. intros. apply H;done. 
- rewrite /=. intros. move : (andP H1)=>[H3 H4].  apply/andP. split; auto. 
Qed.

Lemma contractive_lt : forall (g : gType U) i j, j < i -> contractive_i i g -> contractive_i j g.
Proof.
elim.
- rewrite /=. done.
- rewrite /=. move=> v i j /ltP H /leP H1. apply/leP. lia.
- rewrite /=.  intros. apply : (H i.+1 j.+1). done. done.
- rewrite /=.  intros. apply/allP. move=> gs' Hin. move : (allP H1)=>H2. 
  apply H2 in Hin. done. 
- rewrite /=.  intros. done.
- rewrite /=. intros. move : (andP H2)=>[H3 H4]. apply/andP. split;eauto. 
Qed.

Lemma contractive_0 : forall (g : gType U) i,  contractive_i i g -> contractive g.
Proof.
move=> g. case. done. intros.  apply : contractive_lt; last eauto. done.
Qed.

Lemma bound_contractive_subst : forall (g g': gType U) i j, bound_i (S i) g -> contractive_i j g -> bound g' -> (forall j, contractive_i j g') -> 
contractive_i j (substitution i g g').
Proof.
elim. 
- rewrite /=. done.
- rewrite/=. move => v g' i j. case : (eqVneq v i).  done. simpl. done.
- rewrite /=. intros. apply H. done. done. done. done. 
- rewrite /=. intros. apply/allP. move=> gsub Hin. move : (mapP Hin). case. 
intros. subst. apply H. by apply/InP. move : (allP H0). 
move => H4. apply H4 in p. done. move : (allP H1). move => H4. apply H4 in p. done. done. 
  intros. done.
- rewrite /=. intros. 
apply H. done. done. done. done. 
- rewrite /=. intros.  apply/andP. move : (andP H1) (andP H2)=> [] + +[]. intros. split; auto. 
Qed.


Lemma bound_cont_eq : forall (g : gType U) i, bound_i i g -> contractive_i i g -> (forall j, contractive_i j g).
Proof.
elim; rewrite/=;auto.
- rewrite /=. move => v i /ltP + /leP. lia. 
- rewrite /=. intros. eauto. 
- intros. move : (andP H1) (andP H2)=>[] + + []. intros. apply/andP. split; eauto. 
Qed.

Unset Implicit Arguments. 
Obligation Tactic := intros;try solve [constructor 1; done | constructor 2; done].
Equations tree_of_aux (g : gType U) (P : gt_pred 0 0 g) (l : seq nat):  (option action * seq nat) by wf (size l , mu_height  g)  :=
  tree_of_aux (GRec g0) P l := let: (t,l') := tree_of_aux g0[GRec g0] _  l in (t,size l::l');
  tree_of_aux (GMsg a u g0) _ ([::])  := (Some a,[::]);
  tree_of_aux (GBranch a gs) _ ([::])  := (Some a, [::]);
  tree_of_aux (GMsg a u g0) P (0::l') := tree_of_aux g0 P l';
  tree_of_aux (GBranch a gs) P (i::l') := tree_of_aux (nth GEnd gs i) _ l';
  tree_of_aux (GPar g0 g1) P (0::l') := tree_of_aux g0 _ l';
  tree_of_aux _ _ _ := (None,[::]).
Next Obligation.
move : (andP P). case;intros. apply/andP. split. 
- apply bound_subst. done. done. 
- apply bound_contractive_subst. done. apply : contractive_0. eauto. done. apply : bound_cont_eq. 
  simpl. apply a. done. 
Defined.
Next Obligation.
intros. constructor 2. apply/ltP.  rewrite contractive_mu_height //=. move : (andP P)=> []. done.
Defined.
Next Obligation.
generalize dependent gs. induction i;intros. 
- destruct gs. rewrite /=. done. move : P. 
  rewrite /=. move/andP =>[]. move/andP => [] H0 H1. move/andP => [] H2 H3. apply/andP. split. done.  done.
- destruct gs. rewrite /=. done. move : P. 
  rewrite /=. move/andP => []. intros. apply IHi. rewrite /=. apply/andP. split. move : (andP a0) =>[]. done. 
  move : (andP b) => [];auto.  done.  
Defined.
Next Obligation.
rewrite /=.  intros. move : (andP P) => []. move/andP=>[]  + + /andP => + + []. intros.  apply/andP. split;done. 
Defined.
Set Implicit Arguments.

Definition tree_trace_of (g : gType U) : seq nat -> (option action) * seq nat := 
if @idP ((bound g) && (contractive g)) is ReflectT P 
  then tree_of_aux g P
  else fun _ => (None,[::]).

Definition tree_of (g : gType U) : seq nat -> option action := fun l => fst (tree_trace_of g l).

Definition trace_of (g : gType U) : seq nat -> seq nat := fun l => snd (tree_trace_of g l).

Definition tree_of_without (g g_minus : gType U) (l : seq nat) :=
  if (tree_of g_minus l) is None then (tree_of g l) else None.


 

Definition undef_from (f : seq nat -> option action) (n : nat) : Prop := forall n' l, f ((n + n')::l) = None. 
Notation " f '^^' n " := (undef_from f n)(at level 0).

Inductive TreeOf : gType U -> (seq nat -> option action) -> Prop :=
| TO_msg a u g0 f  : f nil = Some a ->  f^^1 -> TreeOf g0 (fun l => f (0::l)) ->  TreeOf (GMsg a u g0) f
| TO_branch a gs f  : f nil = Some a -> f^^(size gs) -> (forall i g, nth_error gs i = Some g -> TreeOf g (fun l => f (i::l))) -> TreeOf (GBranch a gs) f
| TO_par g0 g1 f : f nil = None -> f^^2 -> TreeOf g0 (fun l => f (0::l)) -> TreeOf g1 (fun l => f (1::l)) -> TreeOf (GPar g0 g1) f
| TO_rec g f : TreeOf (g[GRec g]) f -> TreeOf (GRec g) f
| TO_var f  n : (forall l, f l = None) -> TreeOf (var_gType n) f
| TO_end f  : (forall l, f l = None) -> TreeOf GEnd f.

Variant tree_of_spec g : (seq nat -> option action) -> Prop :=
| TreeOfSpec f : (if bound g && contractive g then TreeOf g f else f = (fun _ => None)) -> tree_of_spec g f.

Lemma treeOfP : forall (g : gType U), tree_of_spec g (tree_of g). 
Proof.
intros. constructor. 
Admitted.

Definition pred_of_tree (f : seq nat -> option action) := fun (l : seq nat) => (f l != None).
Canonical gType_predType := PredType (pred_of_tree :  (seq nat -> option action) -> pred (seq nat)).



End TreeOf.

Notation "Tr^ G" := (tree_of G)(at level 1, format "Tr^ G").
Notation "Tr^ G \ G0 " := (tree_of_without G G0)(at level 1, G at next level, format "Tr^ G \ G0").



(*
Lemma tree_ofP (g : cgType) : TreeOf g (tree_of g).
Proof.
case : g. simpl.  induction g;simpl;intros.
- constructor. intros. case : l;intros;  simp tree_of_aux. done. done.  
- constructor.  intros. simp tree_of_aux. done. 
- constructor. simp tree_of_aux. Search "tree_of_aux". 
  Set Printing All. 
  rewrite tree_of_aux_equation_3. caserewrite /=. 
  rewrite /g_next. unfold g_next_subproof. dependent rewrite nth_nil. /nth -/nth. 
  rewrite /=. rewrite nth_nil. unfold g_next_subproof. dependent rewrite nth_nil. simp tree_of
induction g. 
unfold tree_of. destruct g.
depelim g. 
- constructor. intros. case : l;intros;  simp tree_of_aux. done. done.  
- constructor.  intros. simp tree_of_aux. done. 
- constructor. simp tree_of_aux. rewrite /=. caserewrite /=. 
  rewrite /g_next. unfold g_next_subproof. dependent rewrite nth_nil. /nth -/nth. 
  rewrite /=. rewrite nth_nil. unfold g_next_subproof. dependent rewrite nth_nil. simp tree_of_aux. simp treeintr(tree_of_aux g i). induction g. 
- constructor. intros. case : l.  
 + simp tree_of_aux. rewrite /=. done. 
 + intros. simp tree_of_aux. rewrite /=. generalize dependent n. case. intros. simpl. rewrite /=. Search _ nth. simpl. funelim (tree_of_aux g i). simpl. Set Printing All. Check Sub. reflexivity. Check i. with i. destruct i. Search _ valP. Check valP. cbn. 
funelim (tree_of_aux g). (tree_of_aux g (valP (CGType i))). (tree_of_aux g _).*)
 
(*
Finish obligations
Define wrapper function that expects are cgType 

Define variant specification 

fill in the specification 

Continue on to other specifications
- Define specifications, either custom or using reflect if its a boolean function 

When going to unrolled types, show that the functions now are finite, use that in some smart reflection way


*)














(*A non contractive global type, may first be problematic later after an action prefix, e.g. a. mu t.t
  so a non-contractive gt might have a reduction that avoids the bad part, making TreeOf derivable
  Need a specification for contractivenessSyn

  Define subType of G, G_no_rec. 
  Show that for any G_no_rec, there is a labels_of, returning
  the finite list of labels that return nodes
  also give its specification with the reflect predicate
  
  Show (unfold_i i G) can be cast into G_no_rec 
  
  Now that the function has finite domain, it can be total
  labels_of G,
*)

(*
Lemma nth_error_nil : forall A n, nth_error (@nil A) n = None.
Proof.
intros. case : n.  done. done.
Qed. 

Lemma nth_error_cons : forall A (a : A) n, nth_error ([::a]) (S n) = None.
Proof.
intros. rewrite /=. by rewrite nth_error_nil. 
Qed. 
Locate edivn_spec.

Variant tree_of_spec (g : gType U) (l : seq nat) : option node -> Type :=
 TreeOfSpec n of TreeOf g l n : tree_of_spec g l (Some n).

Lemma tree_ofP g l : tree_of_spec g l (tree_of g l). 
Proof. Admitted.

Lemma tree_of_spec2 : forall g l n, (TreeOf g l n) <-> (tree_of g l == Some n).
Proof.
intros. split. Print Bool.reflect.
move/tree_ofP. 
- elim;intros; simp tree_of; try done. 
 + rewrite /g_next. rewrite H. rewrite /=. done. 
 + destruct idP.
  * done. 
  * move : n1. done.
- funelim (tree_of g l); rewrite -Heqcall; rewrite /=; try done.
 + rewrite nth_error_nil /=. done.
 + case. by move=><-.
 + rewrite nth_error_nil /=. done.
 + destruct idP.
  * simpl in H.  move : H i n. intros. constructor. by simpl. by apply H.  
  * done. 
 + case. move=><-. done. 
 + destruct n.
  * rewrite /=. intros. constructor. apply H. done. 
  * rewrite nth_error_cons /=. done. 
  * case. move=><-. done. 
  * intros. destruct (nth_error l0 n) eqn:Heqn.  
   ** econstructor. eapply Heqn. apply H. simpl in H0. done.  
   ** done. 
  * case. move=><-. done. 
  * destruct n;intros.
   **  constructor. apply H. move : H0. rewrite /=. done. 
   ** move : H0. rewrite /=.  destruct n. 
    *** rewrite /=. intros. constructor. apply H. done. 
    *** rewrite /= nth_error_nil. done. 
Qed.

Definition pred_of_gType (g : gType U) := fun (l : seq nat) => (tree_of g l != None).
Canonical gType_predType := PredType (pred_of_gType : gType U -> pred (seq nat)).

Check (nil \in GEnd). Locate PredType.

Lemma membership_spec : forall g l, (exists n, TreeOf g l n) <-> l \in g.
intros. split. 
- case. intros. apply tree_of_spec in p. unfold mem, in_mem.  rewrite /=. unfold pred_of_gType. 
  rewrite p. done. 
- unfold mem, in_mem. rewrite /=. unfold pred_of_gType. destruct (tree_of g l) eqn:Heqn. intro. exists n.  
  apply tree_of_spec. done. done. 
Qed.*)


