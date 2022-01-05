(*Require Export Dep.fintype. *)

From mathcomp Require Import all_ssreflect.
From Equations Require Import Equations.
From mathcomp Require Import fintype.
From deriving Require Import deriving.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive ptcp  : Set :=
  | Ptcp : nat   -> ptcp .

Definition nat_of_ptcp (p : ptcp) := let: Ptcp n := p in n.
Canonical ptctp_newType := Eval hnf in [newType for nat_of_ptcp]. Locate SubEqMixin.
Definition ptcp_eqMixin := [eqMixin of ptcp by <:]. 
Canonical ptcp_eqType := Eval hnf in EqType ptcp ptcp_eqMixin.
(*Definition ptcp_choiceMixin := [choiceMixin of ptcp by <:].
Canonical ptcp_ChoiceType := Eval hnf in ChoiceType ptcp ptcp_choiceMixin.
Definition ptcp_countMixin := [countMixin of ptcp by <:].
Canonical ptcp_countType := CountType ptcp ptcp_countMixin.*)


Inductive ch  : Set :=
  | Ch : nat   -> ch .

Definition nat_of_ch (c : ch) := let: Ch n := c in n.
Canonical ch_newType := Eval hnf in [newType for nat_of_ch].
Definition ch_eqMixin := [eqMixin of ch by <:]. 
Canonical ch_eqType := Eval hnf in EqType ch ch_eqMixin. 
(*Definition ch_choiceMixin := [choiceMixin of ch by <:].
Canonical ch_ChoiceType := Eval hnf in ChoiceType ch ch_choiceMixin.
Definition ch_countMixin := [countMixin of ch by <:].
Canonical ch_countType := CountType ch ch_countMixin.*)


Inductive action  : Set := Action of ptcp & ptcp & ch.

Definition prod_of_action (a : action) := let '(Action p0 p1 c) := a in (p0,p1,c). 
Definition action_indDef := [indDef for action_rect].
Canonical action_indType := IndType action action_indDef.
Definition action_eqMixin := [derive eqMixin for action].
Canonical action_eqType := EqType action action_eqMixin.
(*Definition action_choiceMixin := [derive choiceMixin for action].
Canonical action_choiceType := ChoiceType action action_choiceMixin.
Definition action_countMixin := [derive countMixin for action].
Canonical action_countType := CountType action action_countMixin.*)


Section Label.
Variable (U:Set).
Inductive label : Set := 
 | LV : action -> U -> label
 | LN : action -> nat -> label.

Definition in_action (a : action) := fun p => let: (Action p0 p1 _) := a in (p == p0) || (p == p1).

Definition pred_of_label (l : label) := fun (p : ptcp) =>
match l with
 | LV a _ => in_action a p
 | LN a _ => in_action a p
end.  

Canonical label_predType := PredType (pred_of_label : label -> pred ptcp).
End Label.


Section GlobalType.
Variable (U : eqType).

Unset Elimination Schemes.
Inductive gType  :=
  | var_gType : nat -> gType
  | GEnd : gType
  | GRec : gType -> gType
  | GMsg : action -> U -> gType-> gType
  | GBranch : action  -> seq gType -> gType
  | GPar : gType -> gType -> gType.

(*From Francisco*)
Set Elimination Schemes. 
Lemma gType_ind :
  forall (P : gType -> Prop),
    P GEnd ->
    (forall v, P (var_gType v)) ->
    (forall G, P G -> P (GRec G)) ->
    (forall a gs, (forall g, List.In g gs -> P g) -> P (GBranch a gs)) ->
    (forall a u g0, P g0 -> P (GMsg a u g0)) ->
    (forall g0 g1, P g0 -> P g1 -> P (GPar g0 g1)) ->
    forall g : gType, P g.
Proof.
  move=> P P_end P_var P_rec P_branch P_msg P_par. fix Ih 1; case.
  + by apply: P_var.
  + by apply: P_end.
  + by move=>G; apply: P_rec.
  + move=> a s g; apply: P_msg. done. 
  + move => a l. apply P_branch. intros. elim : l H. 
   * simpl. contradiction. 
   * move=> a0 l H. simpl. case. move =><-. apply Ih. done. 
  + move => g g0. by apply : P_par. 
Qed.

Fixpoint gType_eqb g0 g1 := 
let list_eq := fix list_eq s1 s2 {struct s1} := 
                                 match s1,s2 with
                                  | [::] , [::] => true 
                                  | x1 :: s1', x2 :: s2' =>  gType_eqb x1 x2 && (list_eq s1' s2') 
                                  | _ , _ => false 
                                  end
in
match g0, g1 with
| GMsg a0 v0 g0', GMsg a0' v0' g1' => (a0 == a0') && (v0 == v0') && (gType_eqb g0' g1') 
| GRec g0', GRec g1' => gType_eqb g0' g1' 
| GEnd, GEnd => true
| GPar g0' g0'', GPar g1' g1'' => (gType_eqb g0' g1') && (gType_eqb g0'' g1'')
| GBranch a gs, GBranch a' gs' => (a == a') && (list_eq gs gs')
| var_gType n, var_gType n' => n == n'
| _, _ => false
end.

Ltac case_filter :=  case;try (rewrite /= ; constructor ; done);intros.
Ltac case_filter_on x := generalize dependent x;case_filter.
Ltac inj := split; solve [ by move/eqP=>-> | by case; move=>->].

Ltac inject :=  split; [ by move=>-> | by case ].
Ltac inject2 :=  split;[ case; by move =>->-> | case;by move =>->-> ]. 
Ltac inject3 := split; [ case;  move=>->; case; move=>->->; done |  case; move =>->->->; done]. 



Lemma reflexive_gType :  reflexive gType_eqb.
Proof. unfold reflexive.
elim;try solve [ rewrite /= ; done].
- intros. rewrite /=. induction gs; first by rewrite eqxx.
  rewrite eqxx /=. apply/andP. split. apply H. simpl. auto. 
  have : (forall g, List.In g gs -> gType_eqb g g). intros. apply H. simpl; auto. 
  move/IHgs. move/andP => [] _. done. 
- intros. by rewrite /= !eqxx H. 
- intros. by rewrite /= H H0.
Qed.


Lemma gType_eqb_axiom : Equality.axiom gType_eqb.
Proof.
unfold Equality.axiom. intros.  apply Bool.iff_reflect.
generalize dependent y. generalize dependent x.
elim. 
- case_filter.
- move=>n. case_filter. rewrite /=. split. case; first by (move=>->; rewrite eqxx). 
  move/eqP=>->. done.
- move=> g Hg. case_filter. split. 
 * case; first (move=>->; rewrite /=). by rewrite reflexive_gType. 
 * rewrite /=. rewrite <- Hg. move=>->. done.
- move => a gs H. case_filter. split.
 * case. move=>->->. by rewrite reflexive_gType. 
 * intros. f_equal. simpl in H0. by move : (andP H0) =>[]=>/eqP. simpl in H0. 
   move : (andP H0)=>[] _. clear H0. generalize dependent l.  induction gs;case_filter.  done. 
   done. 
   move : (andP b). case. move/H=>H1 H2. rewrite H1. f_equal. apply IHgs. 
   intros. apply H. simpl. auto. done. simpl;auto. 
-
 move=> a u g0 H. case_filter. split. case. move=>->->->. rewrite reflexive_gType. done.
 rewrite /=. move/andP=>[]/andP[]/eqP +/eqP=>->->. move/H=>->. done. 
- move=> g0 g1 H0 H1. case_filter. rewrite /=. split. case. move=>->->.
  rewrite !reflexive_gType. done.
  move/andP=>[] /H0 + /H1=>->->.  done.
Qed.
 

Definition gType_eqMixin := EqMixin gType_eqb_axiom. 
Canonical gType_EqType := EqType gType gType_eqMixin.

Fixpoint bound_i (i : nat) (g : gType) := 
match g with 
| GEnd => true
| GMsg _ _ g0 => bound_i i g0
| GBranch _ gs => all (bound_i i) gs
| GPar g0 g1 => (bound_i i g0) && (bound_i i g1)
| GRec g0 => bound_i (S i) g0
| var_gType n => n < i
end.

(*Inspired by Francisco*)
Fixpoint contractive_i (d : nat) (g : gType) :=
match g with 
| GEnd => true
| GMsg _ _ g0 => contractive_i 0 g0
| GBranch _ gs => all (contractive_i 0) gs
| GPar g0 g1 => (contractive_i d g0) && (contractive_i d g1)
| GRec g0 => contractive_i (S d) g0
| var_gType n => d <= n
end. 

(*
Inductive wfgType n := WFgType g of bound_i n g && contractive_i 0 g.
Coercion gType_of_wf n (wfg : wfgType n)  := let: WFgType g _ := wfg in g.
Canonical wfgType_subType n := [subType for (@gType_of_wf n)].
Definition GType := wfgType 0. *)

Fixpoint substitution (i : nat) (g0 g1 : gType) :=
match g0 with
| GMsg a u g0' => GMsg a u (substitution i g0' g1)
| GBranch a gs => GBranch a (map (fun g0' => substitution i g0' g1) gs)
| var_gType n => if n == i then g1 else g0
| GRec g0' => GRec (substitution (S i) g0' g1)
| GPar g0' g1' => GPar (substitution i g0' g1) (substitution i g1' g1)
| GEnd => GEnd
end.

End GlobalType.

Arguments contractive_i {_}.
Arguments bound_i {_}.
Arguments substitution {_}.

Notation bound := (bound_i 0).
Notation contractive := (contractive_i 0).

Notation "G '[' G0 ']'" := (substitution 0 G G0)(at level 0).
Notation gt_pred := (fun n0 n1 g => bound_i n0 g && contractive_i n1 g).



(*Arguments WFgTy<pe {_} {_} {_} _.*)
Arguments GMsg {_}.
Arguments GBranch {_}.
Arguments var_gType {_}.
Arguments GRec {_}.
Arguments GPar {_}.
Arguments GEnd {_}.

Arguments LV {_}.
Arguments LN {_}.


(*Later when we want to do mutual inductive definition with endpoints*)
(*
Inductive test := 
 | Tempt : test
 | TCarry : gType test -> test.

Definition test_pred ( t : test) (n0 n1 : nat) :=
match t with 
| Tempt => true
| TCarry g => bound_i n0 g && contractive_i n1 g
end.

Inductive wftest n0 n1 := WFTest (t : test) of test_pred t n0 n1. 
Check WFTest.
Arguments WFTest {_} {_} _.

Coercion test_of_wf n0 n1 (t : wftest n0 n1) := let: WFTest t0 _ := t in t0.

Canonical wftest_subType n0 n1 := [subType for (@test_of_wf n0 n1)].
*)
