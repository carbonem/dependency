Require Import Dep.Syntax.
Require Import Dep.Tree.
Require Import Lists.List.
From mathcomp Require Import all_ssreflect.
From Equations Require Import Equations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Order.
Variable (U : eqType). 

Definition action_from (a : action) := let : Action p0 _ _ := a in p0.
Definition action_to (a : action) := let : Action _ p1 _ := a in p1.
Definition action_ch (a : action) := let : Action _ _ c := a in c.

Definition II_rel (a0 a1 : action) := (action_from a0 == action_from a1) && (action_ch a0 != action_ch a1).
Definition IO_rel (a0 a1 : action) := (action_to a0 == action_from a1) && (action_ch a0 != action_ch a1).
Definition OO_rel (a0 a1 : action) := (action_from a0 == action_from a1) && (action_ch a0 == action_ch a1).

Definition OO_IO_rel (a0 a1 : action) := OO_rel a0 a1 || IO_rel a0 a1.

Fixpoint postfix (A : eqType) (l0 l1 : seq A) : (seq A) := 
if l0 is x0::l0' then
 if l1 is x1::l1' then if (x0==x1) then postfix l0' l1' else [::]
  else [::]
else l1.

Definition proper_succ (l0 l1 : seq nat) := size (postfix l0 l1) > 1.

Definition opt_rel (o0 o1 : option action) (P : rel action) : bool :=
if o0 is Some a0 
  then if o1 is Some a1 
         then P a0 a1
         else false 
  else false.

Definition label_lt (P : rel action) (f  : seq nat -> option action) (l0 l1 : seq nat) : bool := 
 proper_succ l0 l1 && opt_rel (f l0) (f l1) P.

Notation "n0 ≺[ P ] n1 ∈ T "  := (label_lt P T n0 n1)(at level 70, n1 at next level,format "n0 ≺[ P ] n1 ∈ T" ).

Definition sub_seqs_from A (l0 l : seq A) := foldl (fun ls x => ls ++ [seq rcons l' x  | l' <- ls ]) ([:: l0]) l.

Definition path_btw (l0 l1 : seq nat) := 
if l1 is x1::l1'
  then let l1_post := postfix l0 (belast x1 l1')
       in if sub_seqs_from l0 l1_post is x::l
            then l
            else [::]
  else [::].

Definition paths_btw (l0 l1 : seq nat) :=
if sub_seqs_from nil (path_btw l0 l1) is x::l then l else [::].

Eval compute in (paths_btw ([:: 0 ; 1 ;2]) ([:: 0; 1 ; 2 ; 4 ; 5; 6])). 

Definition in_dep (l l' : seq nat) (g : gType U) := 
  existsb (fun (ls : seq (seq nat)) => if ls is ll::ls' 
                                    then path (fun l0 l1 => l0 ≺[OO_IO_rel] l1 ∈ Tr^g) l (belast ll ls') 
                                         && ((last ll ls') ≺[II_rel] l' ∈ Tr^g)
                                    else l ≺[II_rel] l' ∈ Tr^g)  (paths_btw l l').

Definition InDep  (l l' : seq nat) (g : gType U) := 
(exists ls l,  path (fun l0 l1 => l0 ≺[IO_rel] l1 ∈ Tr^g) l (rcons ls l) && (l ≺[II_rel] l' ∈ Tr^g)).

Lemma in_depP : forall l l' G, reflect (InDep l l' G) (in_dep l l' G).
Proof. Admitted.

Definition out_dep (l l' : seq nat) (g : gType U) := 
  existsb (fun (ls : seq (seq nat)) => path (fun l0 l1 => l0 ≺[OO_IO_rel] l1 ∈ Tr^g) l (rcons ls l'))  (paths_btw l l').

Definition OutDep (l l' : seq nat) (G : gType U) :=  (exists ls,  path (fun l0 l1 => l0 ≺[OO_IO_rel] l1 ∈ Tr^G) l (rcons ls l')).

Lemma out_depP : forall l l' G, reflect (OutDep l l' G)  (out_dep l l' G).
Proof. Admitted.
End Order.

(*repeat notation to use outside of section*)
Notation "n0 ≺[ P ] n1 ∈ T "  := (label_lt P T n0 n1)(at level 70, n1 at next level,format "n0 ≺[ P ] n1 ∈ T" ).

Section Unfold.
Variable (U : eqType).
Unset Implicit Arguments.

(*From Equations Rose Trees example*)
(*A variant of map that expects a membership proof to show recursion is restricted to list members*)
Equations map_In {A B : Type}
     (l : list A) (f : forall (x : A), In x l -> B) : list B :=
  | nil, _ := nil
  | cons x xs, f := cons (f x _) (map_In  xs (fun x H => f x _)).

Lemma map_In_spec {A B : Type} (f : A -> B) (l : list A) :
  map_In l (fun (x : A) (_ : In x l) => f x) = List.map f l.
Proof.
  funelim (map_In l _); rewrite ?H; trivial. simp map_In. simpl. f_equal. done. 
Qed.
Set Implicit Arguments.

  
Fixpoint gType_size (g : gType U) :=
match g with
 | GMsg a u g0 => 1 + (gType_size g0)
 | GRec g0 => 1 + (gType_size g0)
 | GBranch a gs => 1 + (sumn (map gType_size gs))
 | GEnd => 1
 | GPar g0 g1 => 1 + (gType_size g0) + (gType_size g1)
 | var_gType n => 1
end. 

(*Considered unfold_i 0 g to be some special base case, but n ∈ g(0)\g(0) is empty so no problem*)
Equations unfold_i  (i : nat) (g : gType U) : gType U by wf (gType_size g,i)  :=

 unfold_i i (GMsg a u g0) := GMsg a u (unfold_i i g0);
 unfold_i i (GBranch a gs) := GBranch a (map_In gs (fun g H => unfold_i i g));
 unfold_i i GEnd := GEnd;
 unfold_i i (var_gType n) := var_gType n;
 unfold_i 0 (GRec g0) := g0[GEnd];
 unfold_i (S i') (GRec g0) := g0[unfold_i i' (GRec g0)];
 unfold_i i (GPar g0 g1) := GPar (unfold_i i g0) (unfold_i i g1).
Next Obligation.
Proof.
constructor 1. apply/ltP.  generalize dependent g. induction gs;try done. 
rewrite /=. move => g []. 
- move=>->. rewrite -add1n. rewrite !addnA. apply leq_addr.  
  intros. apply IHgs in b;try done. rewrite [gType_size _ + _]addnC.  rewrite addnA. 
  Search _ (_ < _ -> _ < _). apply ltn_addr. done. 
Qed.
Next Obligation.
Proof.
constructor 1. apply/ltP. rewrite -add1n.  apply leq_addr. 
Qed.
Next Obligation.
Proof.
constructor 1. apply/ltP. rewrite -addnA.  rewrite[gType_size _ + _]addnC. rewrite addnA. rewrite -add1n.  
apply leq_addr. 
Qed.
End Unfold.
Arguments unfold_i {_}.
Print seq.
Notation "G [ n ] " := (unfold_i n G)(at level 0, format  "G [ n ]"). 
Check (GEnd[2]).



Section Folding.
Variable (U : eqType).

(*Maybe off by one error*)
Definition folding_of (g : gType U) (label : seq nat) :=
 if rotr 2 (trace_of g label) is i::i'::_ then 
  Some (take ((size label)-i) label ++ drop ((size label)-i') label)
  else None.

Variant folding_of_spec : gType U -> seq nat -> seq nat -> option (seq nat) -> option (seq nat) -> Prop :=
 FoldingOfSpec l0 l1 l2 l3 R g : l0 ≺[R] l1 ∈ Tr^g -> l2 ≺[R] l3 ∈ Tr^g -> folding_of_spec g l0 l1 (Some l2) (Some l3).

Lemma folding_ofP : forall (g : gType U) (l0 l1 : seq nat), folding_of_spec g l0 l1 (folding_of g l0) (folding_of g l1).
Proof. Admitted.

(*
Alternative definition of folding

Definition true_rel (a0 a1 : action) := true.
Inductive folding_of : gType U -> nat -> seq nat -> seq nat -> Prop :=
 | FoldingOf f' f g k i l' l :  f' = Tr^g[k]\g[k-1] -> f = Tr^g[k+i]\g[k+i-1] ->
                           l' \in f' -> l \in f -> 
(forall l_lt, l_lt ≺[true_rel] l ∈ f -> exists l_lt', folding_of g i l_lt' l_lt /\ l_lt' ≺[true_rel] l' ∈ f') ->
(forall l_gt, l ≺[true_rel] l_gt ∈ f -> exists l_gt', folding_of g i l_gt' l_gt /\ l' ≺[true_rel] l_gt' ∈ f') -> folding_of g i l' l.

Check FoldingOf.
Lemma folding_exists : forall (g : gType U) (l : seq nat) n, l \in Tr^g[n.+1]\g[n] -> exists l', folding_of g 1 l' l.
Proof. Admitted.*)
End Folding.

Section Linearity.
Variable (U : eqType).

(*This doesn't apply linearity to carried global types*)
Definition same_ch (a0 a1 : action) := action_ch a0 == action_ch a1.
Definition Linear (g : gType U) := 
forall l0 l1, (l0 ≺[same_ch] l1 ∈ Tr^g) -> in_dep l0 l1 g /\ out_dep l0 l1 g.

(*tree_of (unfold_i i g) is a function with finite domain, maybe define it as a finfun
  with domain as some finite subset of lists 
  Read more : https://hal.inria.fr/inria-00515548v4/document p. 43
*)

(*unfolding more preserves order and relation R*)
Lemma unfold_ps_order : forall l0 l1 (G : gType U) R n k, l0 \in Tr^G[n] -> l1 \in Tr^G[n] -> l0 ≺[R] l1 ∈ Tr^G[n+k] -> l0 ≺[R] l1 ∈ Tr^G[n].
Proof. Admitted.

Lemma in_dep_ps : forall l0 l1 (g : gType U) n k, in_dep l0 l1 g[n] -> l0 \in Tr^g[n] -> l1 \in Tr^g[n] -> in_dep l0 l1 g[n+k].
Proof. Admitted.

Lemma out_dep_ps : forall l0 l1 (g : gType U) n k, out_dep l0 l1 g[n] -> l0 \in Tr^g[n] -> l1 \in Tr^g[n] -> out_dep l0 l1 g[n+k].
Proof. Admitted.

Lemma linear_le : forall n k (g : gType U), Linear g[n+k+1]  -> Linear g[n+1].
Proof. Admitted.

Lemma case_order : forall l1 l2 n (g : gType U), l1 ≺[same_ch] l2 ∈ Tr^g[n.+2] -> 
  l1 \in Tr^g[n.+1] /\ l2 \in Tr^g[n.+1] /\  l1 ≺[same_ch] l2 ∈ Tr^g[n.+2] \/ 
  l1 \in Tr^g[n.+1]\g[n] /\ l2 \in Tr^g[n.+2]\g[n.+1] \/ 
  (exists i, l1 \in Tr^g[n-i]) /\ l2 \in Tr^g[n.+2]\g[n.+1].
Proof.
Admitted.

Lemma linear1_n1 : forall n (g : gType U), Linear g[1]  -> Linear g[n+1].
Proof. 
induction n. 
- intros. done. 
- intros. apply IHn in H. unfold Linear.  
  move => n1 n2. rewrite addn1. move/case_order. case.  
 + move => [] + []. rewrite -{3}addn1.  intros. move : (unfold_ps_order a a0 b).
   unfold Linear in H. rewrite -addn1. move/H. 
   case. intros. rewrite -addn1. split.
  * apply in_dep_ps. done. by rewrite addn1. by rewrite addn1.
  * apply out_dep_ps. done. by rewrite addn1. by rewrite addn1. 
 + case.
  * case. Admitted.

(*
move/folding_exists. case. move=> n1' Hf1.
          move/folding_exists. case. move=> n2' Hf2.
    inversion Hf1. subst.
    inversion Hf2. subst.
    case : Hf1. intros.
    case : Hf1. intros. case : Hunfold move : H2. move : H2 H3=>[] + []. . intros. case : (folding_exists 

rewrite -addn1 -addnA. 
  move/unfold_ps_order. move/a.
  move=>->. change (  f_equal. done. Search _ (?n +1 = ?n.+1). move : (@unfold_ps_order n1 n2 g same_ch  H0). unfold Linear in H. unfold Linear in IHn. split. apply/in_depP. 
   unfold InDep. apply IHn.
 +
split. apply/in_depP.
 * unfold InputDependency. Admitted.
*)

Lemma linear_n : forall (g : gType U), Linear (unfold_i 1 g) <-> Linear g.
Proof.
intros. split. 
 Admitted.

(*TODO: unfold once, then for each label, check its successors
  Need a test for "end of graph", perhaps replace option action with node type again*)
Definition linear (g : gType U) : bool := true.

Lemma linear_reflect : forall g, reflect (Linear g) (linear g).
Proof. Admitted.
