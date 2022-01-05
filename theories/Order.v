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


(*Notation "n ∈ G0 \ G1" := ((n \in G0) && (n \in G1))(at level 70, format "n  ∈  G0 \ '/' G1").
Check (nil ∈ GEnd[2]\GEnd[1]). *)

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
intros. split. apply linear1_n1. 
 Admitted.

(*TODO: unfold once, then for each label, check its successors
  Need a test for "end of graph", perhaps replace option action with node type again*)
Definition linear (g : gType U) : bool := true.

Lemma linear_reflect : forall g, reflect (Linear g) (linear g).
Proof. Admitted.











Definition pred_of_gType (g : gType U) := fun (l : seq nat) => (tree_of g l != None).
Canonical gType_predType := PredType (pred_of_gType : gType U -> pred (seq nat)).

Definition opt_rel (o0 o1 : option action) (P : rel action) : bool :=
if o0 is Some a0 
  then if o1 is Some a1 
         then P a0 a1
         else false 
  else false.

Fixpoint postfix (A : eqType) (l0 l1 : seq A) : (seq A) := 
if l0 is x0::l0' then
 if l1 is x1::l1' then if (x0==x1) then postfix l0' l1' else [::]
  else [::]
else l1.

Definition proper_succ (l0 l1 : seq nat) := size (postfix l0 l1) > 1.

Definition ordered_actions_aux (P : rel action) (g : gType U) (l0 l1 : seq nat) : bool := 
 proper_succ l0 l1 && opt_rel (tree_of g l0) (tree_of g l1) P.

Notation " n0 '≺[' P ']' n1 ∈ G "  := (ordered_actions_aux P G n0 n1)(at level 70).

Inductive orderedLabels l0 l1 G := OrderedLabels of l0 ≺[ fun _ _ => true] l1 ∈ G.
Check OrderedLabels.

Definition sub_seqs A (l0 l : seq A) := foldl (fun ls x => ls ++ [seq rcons l' x  | l' <- ls ]) ([:: l0]) l.
Eval compute in (sub_seqs nil ([:: 0 ; 1 ; 2 ])).
 
Coercion pair_of_orderedLabels l0 l1 G (ol : orderedLabels l0 l1 G) := (l0,l1).

Canonical orderedLabels_subType l0 l1 G := [subType for (@pair_of_orderedLabels l0 l1 G)].


Check (nil ≺[fun a0 a1 => a0 == a1] nil ∈ GEnd).
Check path.
Definition OrderedActionSeqAnd (P : rel action) (g : gType U) (l0 : seq nat) (l : seq (seq nat)) : Prop := 
path (fun n0 n1 => n0 ≺[ P ] n1 ∈ g) l0 l.

Definition action_from (a : action) := let : Action p0 _ _ := a in p0.
Definition action_to (a : action) := let : Action _ p1 _ := a in p1.
Definition action_ch (a : action) := let : Action _ _ c := a in c.

Definition II_rel (a0 a1 : action) := (action_from a0 == action_from a1) && (action_ch a0 != action_ch a1).
Definition IO_rel (a0 a1 : action) := (action_to a0 == action_from a1) && (action_ch a0 != action_ch a1).
Definition OO_rel (a0 a1 : action) := (action_from a0 == action_from a1) && (action_ch a0 == action_ch a1).
Check mask. Locate mask. 

Fixpoint postfix (A : eqType) (l0 l1 : seq A) : option (seq A) := 
if l0 is x0::l0' then
 if l1 is x1::l1' then if (x0==x1) then postfix l0' l1' else None
  else None
else Some l1.
Check rcons.

Fixpoint add_each (l0 l1 : seq nat) :=
if l1 is x1::l1' then 
  let l0' := rcons l0 x1
  in l0'::(add_each l0' l1')
else [::].
Check scanl.

Definition seq_btw (l0 l1 : seq nat) := if postfix l0 l1 is Some l' then Some (scanl (fun a x0 => rcons a x0) l0 l') else None.

Definition sub_seqs_from A (l0 l : seq A) := foldl (fun ls x => ls ++ [seq rcons l' x  | l' <- ls ]) ([:: nil]) l.
Eval compute in (sub_seqs ([:: 0 ; 1 ; 2 ])). 

Variant sub_seqs_spec (A : eqType) : seq A -> seq (seq A) -> Prop :=
| SubSeqsSpec l  ls m : size m = size l -> ((mask m l) \in ls) -> sub_seqs_spec l ls.

Lemma sub_seqsP : forall (A : eqType) (l : seq A) , sub_seqs_spec l (sub_seqs l).
Proof. Admitted.
Check existsb.
Definition out_dep (l0 l1 : seq nat) : bool := existsb (fun sub_s ->  ) sub_seqs l0
Eval compute in (sub_seqs ([:: 0 ; 1 ; 2 ])). 
Definition enum_labels (l0 l1 : seq nat) :=
Eval compute in (seq_btw ([:: 0 ; 1 ; 2 ]) ([:: 0 ; 1 ; 2 ; 3 ;4 ])).

Definition seq_btw l0 l1 := if postfix l0 l1 is Some l' then add_each l0 l' else [::].

Check nil.
Eval compute in (seq_btw ([:: 0 ; 1 ; 2 ]) ([:: 0 ; 1 ; 2 ; 3 ;4 ])).
Definition OutputDependency (g : gType U) (l0 l1 : seq nat) := 

D

Definition InputDependency (g : gType U) (l0 l1 : seq nat) := exists ls l', OrderedActionSeqAnd IO_rel g ([::l0]++ls++[::l']) /\ 
                                                                     OrderedActionsAnd II_rel g l' l1.

Definition OO_IO_rel (a0 a1 : action) := OO_rel a0 a1 || IO_rel a0 a1.
Definition OutputDependency (g : gType U) (l0 l1 : seq nat) := exists ls, OrderedActionSeqAnd OO_IO_rel g ([::l0]++ls++[::l1]).

(*This doesn't apply linearity to carried global types*)
Definition same_ch (a0 a1 : action) := action_ch a0 == action_ch a1.
Definition Linear (g : gType U) := 
forall l0 l1, OrderedActionsAnd same_ch g l0 l1 -> InputDependency g l0 l1 /\ OutputDependency g l0 l1.
End Order.



End Order.






(*Reflection, return to this later*)
Fixpoint seq_prefix (A : eqType) (l0 l1 : seq A) : bool := 
if l0 is x0::l0' then
 if l1 is x1::l1' then (x0==x1) && seq_prefix l0' l1'
  else false 
else true.

(*if l0 is a prefix it will be present as well, maybe prove this*)
(*Definition order_of (g : gType U) (l0 l1 : seq nat) := (l1 \in g) && (seq_prefix l0 l1).*)

(*Lemma order_of_spec : forall g l0 l1, OrderedActions g l0 l1 <-> order_of g l0 l1.
Proof. Admitted. *)
(*Notation "l0 ≺ l1 ∈ G" := (order_of G l0 l1)(at level 0). *)

(*Definition try_apply (f : rel action) (o0 o1 : option node)  :=
if o0 is Some (NAction a0) 
 then if o1 is Some (NAction a1)
  then f a0 a1
  else false 
else false. *)

(*
Definition dependency (f : rel action) (g : gType U) (l0 l1 : seq nat) := 
l0 ≺ l1 ∈ g && try_apply f (tree_of g l0) (tree_of g l1).*)

(*
Notation " n0 '≺_II' n1 ∈ G "  := (dependency II_aux G n0 n1)(at level 0).
Notation " n0 '≺_IO' n1 ∈ G "  := (dependency IO_aux G n0 n1)(at level 0).
Notation " n0 '≺_OO' n1 ∈ G "  := (dependency OO_aux G n0 n1)(at level 0).
*)

(*
Alternative definition of tree, more intuitive
Fixpoint tree_of (g : gType) (l : seq nat) : option node :=
match g with 
| GEnd => if l is [::] then Some NEnd else None
| GPar g0 g1 => match l with 
               | [::] => NPar
               | n::l' => tree_of (nth_error [::g0;g1] n)
               end
| GMsg a _ g0 => match l with 
               | [::] => NAction a
               | n::l' => tree_of (nth_error [::g0] n)
| GBranch a gs => match l with 
               | [::] => NAction a
               | n::l' => tree_of (nth_error gs n) l'

| GRec g0 => tree_of (g0[(GRec g0);;ids]) l
| var_gType _ => fun _ => None
end. *)


(* Spec for tree_of function
Inductive tree_of : gType -> seq nat -> node -> Prop :=
| to_end : tree_of GEnd nil NEnd
| to_par_nil g0 g1 : tree_of (GPar g0 g1) nil NPar
| to_par_cons0 g0 g1 n l : tree_of g0 l n -> tree_of (GPar g0 g1) (0::l) n
| to_par_cons1 g1 l n g0 : tree_of g1 l n -> tree_of (GPar g0 g1) (1::l) n
| to_msg_nil a u g0 : tree_of (GMsg a u g0) nil (NAction a)
| to_msg_cons0 g0 l n a u : tree_of g0 l n -> tree_of (GMsg a u g0) (0::l) n
| to_branch_nil a gs : tree_of (GBranch a gs) nil (NAction a)
| to_branch_consn l n' no (gs : n'.-tuple gType) (n : 'I_n') a : tree_of (tnth gs n) l no -> tree_of (GBranch a gs) ((n:nat)::l) no
| to_rec : g0' = g0 [GRec g0 ..;;ids] -> tree_of g0' l n-> tree_of (GRec g0) l n.
*)

(*Inductive ActionOrder : gType U -> seq nat -> seq nat -> Prop := 
| AO_msg_nil a u g0 l1: (exists n, TreeOf g0 l1 n)  -> ActionOrder (GMsg a u g0) nil (0::l1)
| AO_msg_cons l0 a u g0 l1: ActionOrder g0 l0 l1 -> ActionOrder (GMsg a u g0) (0::l0) (0::l1)
| AO_branch_nil i g gs a l1: nth_error gs i = Some g -> (exists n, TreeOf g l1 n) -> ActionOrder (GBranch a gs) nil (i::l1)
| AO_branch_cons i g gs a l0 l1: nth_error gs i = Some g -> ActionOrder g l0 l1 -> ActionOrder (GBranch a gs) (i::l0) (i::l1)
| AO_par0 g0 g1 l0 l1: ActionOrder g0 l0 l1 -> ActionOrder (GPar g0 g1) (0::l0) (0::l1)
| AO_par1 g0 g1 l0 l1: ActionOrder g1 l0 l1 -> ActionOrder (GPar g0 g1) (1::l0) (1::l1)
| AO_rec g0 l0 l1 : contractive (GRec g0) -> ActionOrder (g0[GRec g0]) l0 l1 ->  ActionOrder (GRec g0) l0 l1.*)

(*Definition OrderedActionSeq (g : gType U) (l : seq (seq nat)) := 
forall i l0 l1, nth_error l i = Some l0 -> nth_error l (S i) = Some l1 -> OrderedActions g l0 l1.*)


(*Fixpoint seq_prefix (A : eqType) (l0 l1 : seq A) : bool := 
if l0 is x0::l0' then
 if l1 is x1::l1' then (x0==x1) && seq_prefix l0' l1'
  else false 
else true.

Lemma seq_prefix_spec : forall (A : eqType) (l0 l1 : seq A), (exists l, l0++l=l1 : Prop) <-> (seq_prefix l0 l1).
Proof.
induction l0.
- rewrite /=. intros. split; eauto. 
- case. 
 + rewrite /=. split. case. done. done. 
 + intros. rewrite /=. case : (eqVneq a a0). 
  * rewrite /=. move=>H. split.
   **  case. intros. apply IHl0. eauto. case : p. intros. eauto. 
   ** move/IHl0. case. intros. exists x. subst. done. 
  * rewrite /=. intros. split.
   ** case. move=> x. case. move : i.  move/eqP. done. 
   ** done. 
Qed.

Lemma seq_prefix_reflect : forall (A : eqType) (l0 l1 : seq A), reflect (exists l, l0++l = l1) (seq_prefix l0 l1).
Proof.
intros. destruct (seq_prefix l0 l1) eqn:Heqn. apply seq_prefix_spec in Heqn.
constructor. done.
constructor. intro. apply seq_prefix_spec in H. rewrite Heqn in H. done. 
Qed.*)
