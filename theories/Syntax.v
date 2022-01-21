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
Canonical ptctp_newType := Eval hnf in [newType for nat_of_ptcp]. 
Definition ptcp_eqMixin := [eqMixin of ptcp by <:]. 
Canonical ptcp_eqType := Eval hnf in EqType ptcp ptcp_eqMixin.
Definition ptcp_choiceMixin := [choiceMixin of ptcp by <:].
Canonical ptcp_ChoiceType := Eval hnf in ChoiceType ptcp ptcp_choiceMixin.
Definition ptcp_countMixin := [countMixin of ptcp by <:].
Canonical ptcp_countType := CountType ptcp ptcp_countMixin.


Inductive ch  : Set :=
  | Ch : nat   -> ch .

Definition nat_of_ch (c : ch) := let: Ch n := c in n.
Canonical ch_newType := Eval hnf in [newType for nat_of_ch].
Definition ch_eqMixin := [eqMixin of ch by <:]. 
Canonical ch_eqType := Eval hnf in EqType ch ch_eqMixin. 
Definition ch_choiceMixin := [choiceMixin of ch by <:].
Canonical ch_ChoiceType := Eval hnf in ChoiceType ch ch_choiceMixin.
Definition ch_countMixin := [countMixin of ch by <:].
Canonical ch_countType := CountType ch ch_countMixin.


Inductive action  : Set := Action of ptcp & ptcp & ch.

Definition prod_of_action (a : action) := let '(Action p0 p1 c) := a in (p0,p1,c). 
Definition action_indDef := [indDef for action_rect].
Canonical action_indType := IndType action action_indDef.
Definition action_eqMixin := [derive eqMixin for action].
Canonical action_eqType := EqType action action_eqMixin.
Definition action_choiceMixin := [derive choiceMixin for action].
Canonical action_choiceType := ChoiceType action action_choiceMixin.
Definition action_countMixin := [derive countMixin for action].
Canonical action_countType := CountType action action_countMixin.

Section GlobalType.
Variable (U : countType).

Unset Elimination Schemes.
Inductive gType  :=
  | GVar : nat -> gType
  | GEnd : gType
  | GRec : gType -> gType
  | GMsg : action -> U -> gType-> gType
  | GBranch : action  -> seq gType -> gType.
Set Elimination Schemes. 

Section Elimination.

Variables (Pg : gType -> Type) 
          (P_glist : seq gType -> Type).

Hypothesis Pg_var : (forall n : nat, Pg (GVar n)).
Hypothesis Pg_end : Pg GEnd.
Hypothesis Pg_rec : (forall g : gType, Pg g -> Pg (GRec g)).
Hypothesis Pg_msg : (forall (a : action) (u : U) (g : gType), Pg g -> Pg (GMsg a u g)).
Hypothesis Pg_branch : (forall (a : action) (l : seq gType), P_glist l  -> Pg (GBranch a l)).

Hypothesis P_glist_0 : P_glist nil.
Hypothesis P_glist_cons : forall g, Pg g -> forall l, P_glist l -> P_glist (g::l).

Definition gType_rect : forall g, Pg g :=
fix gType_rect g :=
  let fix seq_gType_rect gs : P_glist gs := 
    match gs with 
     | [::] => P_glist_0
     | g'::gs' => P_glist_cons (gType_rect g') (seq_gType_rect gs') 
     end in
  match g with 
   | GVar n => Pg_var n
   | GEnd => Pg_end
   | GRec g => Pg_rec (gType_rect g)
   | GMsg a u g => Pg_msg a u (gType_rect g)
   | GBranch a l => Pg_branch a (seq_gType_rect l)
   end.

Definition seq_gType_rect : forall gs, P_glist gs :=
 fix seq_gType_rect gs : P_glist gs := 
    match gs with 
     | [::] => P_glist_0
     | g'::gs' => P_glist_cons (gType_rect g') (seq_gType_rect gs') 
     end.


End Elimination.

Combined Scheme mut_rect from gType_rect, seq_gType_rect.
Definition mut_ind_indDef := [indDef for mut_rect].
Canonical gType_indType := IndType gType mut_ind_indDef.
Definition gType_eqMixin := [derive eqMixin for gType].
Canonical gType_eqType := EqType gType gType_eqMixin.
Definition gType_choiceMixin := [derive choiceMixin for gType].
Canonical gType_choiceType := ChoiceType gType gType_choiceMixin.
Definition gType_countMixin := [derive countMixin for gType].
Canonical gType_countType := CountType gType gType_countMixin.
Check mut_rect.

Definition gType_ind P := @gType_rect P (fun gs => forall (g : gType), true ).

(*Remove vacously true sub goal from principle*)
Lemma gType_ind_list P : 
       (forall n : nat, P (GVar n)) ->
       P GEnd ->
       (forall g : gType, P g -> P (GRec g)) ->
       (forall (a : action) (u : U) (g : gType), P g -> P (GMsg a u g)) ->
       (forall (a : action) (l : seq gType),
        (forall g : gType_eqType, g \in l -> P g) -> P (GBranch a l)) ->
       (forall g : gType,
        P g ->
        forall l : seq gType,
        (forall g0 : gType_eqType, g0 \in l -> P g0) ->
        forall g0 : gType_eqType, g0 \in g :: l -> P g0) -> 
       forall g : gType, P g.
Proof. 
intros. move : g. apply : (@gType_rect P (fun gs => forall g, g \in gs -> P g));auto.
move => g. rewrite in_nil. done.
Qed.


Definition gType_rec_list P := @gType_ind_list P. 

Fixpoint bound_i (i : nat) (g : gType) := 
match g with 
| GEnd => true
| GMsg _ _ g0 => bound_i i g0
| GBranch _ gs => all (bound_i i) gs
(*| GPar g0 g1 => (bound_i i g0) && (bound_i i g1)*)
| GRec g0 => bound_i (S i) g0
| GVar n => n < i
end.

(*Inspired by Francisco*)
Fixpoint contractive_i (d : nat) (g : gType) :=
match g with 
| GEnd => true
| GMsg _ _ g0 => contractive_i 0 g0
| GBranch _ gs => all (contractive_i 0) gs
(*| GPar g0 g1 => (contractive_i d g0) && (contractive_i d g1)*)
| GRec g0 => contractive_i (S d) g0
| GVar n => d <= n
end. 



Fixpoint substitution (i : nat) (g0 g1 : gType) :=
match g0 with
| GMsg a u g0' => GMsg a u (substitution i g0' g1)
| GBranch a gs => GBranch a (map (fun g0' => substitution i g0' g1) gs)
| GVar n => if n == i then g1 else g0
| GRec g0' => GRec (substitution (S i) g0' g1)
(*| GPar g0' g1' => GPar (substitution i g0' g1) (substitution i g1' g1) *)
| GEnd => GEnd
end.

End GlobalType.

Arguments contractive_i {_}.
Arguments bound_i {_}.
Arguments substitution {_}.

Notation bound := (bound_i 0).
Notation contractive := (contractive_i 0).

Notation "G [ G0 ]" := (substitution 0 G G0)(at level 0, format "G [ G0 ]").

Notation gt_pred := (fun n0 n1 g => bound_i n0 g && contractive_i n1 g).



(*Arguments WFgTy<pe {_} {_} {_} _.*)
Arguments GMsg {_}.
Arguments GBranch {_}.
Arguments GVar {_}.
Arguments GRec {_}.
(*Arguments GPar {_}.*)
Arguments GEnd {_}.

Definition linear_spec := 
forall (g0 g1 : gType U), (exists2 p, path (grel g_next) g p & g0 = last g p) ->
                     (exists2 p, path (grel g_next) g p & g1 = last g p) ->
                     (exists2 p, path (grel g_next) g0 p & g1 = last g0 p) ->
                     opt_rel g0 g1 same_ch -> in_dep_spec g0 g1 /\ out_dep_spec g0 g1.



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
