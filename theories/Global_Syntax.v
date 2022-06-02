(*Require Export Dep.fintype. *)

From mathcomp Require Import all_ssreflect zify.
From Equations Require Import Equations.
From deriving Require Import deriving. Locate In.

From Dep Require Export Utils. 
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

Definition ptcp_from (a : action) := let : Action p0 _ _ := a in p0.
Definition ptcp_to (a : action) := let : Action _ p1 _ := a in p1.
Definition action_ch (a : action) := let : Action _ _ c := a in c.


Inductive dir := Sd | Rd.

Definition dir_eq (d0 d1 : dir) := 
match d0,d1 with 
| Sd,Sd => true 
| Rd,Rd => true
| _,_ => false 
end.

Check Equality.axiom.

Lemma dir_axiom : Equality.axiom dir_eq. 
Proof.
rewrite /Equality.axiom. move => [] []; rewrite /=;try done;auto. constructor. done. constructor. done. intros. 
constructor.  done. constructor. done.
Qed.
Check EqMixin.
Definition dir_mixin := EqMixin  dir_axiom.
Canonical dir_eqType := EqType dir dir_mixin.


Unset Elimination Schemes. Check seq.
Inductive gType  : Set :=
  | GVar : nat -> gType  
  | GEnd : gType  
  | GRec : nat -> gType -> gType  
  | GMsg : action -> value -> gType -> gType  
  | GBranch : action -> seq gType -> gType  
 with value  : Set  :=
  | VSeqSort : seq mysort -> value  
  | VLT : endpoint -> ptcp  -> value  
 with mysort  : Set :=
  | SBool : mysort
  | SNat : mysort  
  | SGType : gType -> mysort (*maybe more sorts?*)
 with endpoint  : Set :=
  | EVar : nat -> endpoint  
  | EEnd : endpoint  
  | EMsg : dir -> ch -> value -> endpoint -> endpoint  
  | EBranch  : dir -> ch  -> seq endpoint -> endpoint  
  | ERec : nat -> endpoint -> endpoint .
Set Elimination Schemes.


(*It is hard to give a mutually inductive nested induction principle*)
(*
Scheme gType_ind := Induction for gType Sort Prop 
with value_ind := Induction for value Sort Prop 
with mysort_ind := Induction for mysort Sort Prop 
with endpoint_ind := Induction for endpoint Sort Prop.

Check gType_ind.
Combined Scheme gvme_ind from gType_ind,value_ind,mysort_ind,endpoint_ind.
*)



Section Elimination.

Variables (Pg : gType -> Type) 
          (Pv : value -> Type) 
          (Pe : endpoint -> Type) 
          (Pm : mysort -> Type)
          (P_glist : seq gType -> Type)
          (P_elist : seq endpoint -> Type)
          (P_mlist : seq mysort -> Type).

Hypothesis Pg_var : (forall n : nat, Pg (GVar n)).
Hypothesis Pg_end : Pg GEnd.
Hypothesis Pg_rec : (forall g : gType, Pg g -> forall n, Pg (GRec n g)).
Hypothesis Pg_msg : (forall (a : action) (v : value), Pv v -> forall g : gType, Pg g -> Pg (GMsg a v g)).
Hypothesis Pg_branch : (forall (a : action) (l : seq gType), P_glist l  -> Pg (GBranch a l)).

Hypothesis Pv_vst : forall l : seq mysort, P_mlist l -> Pv (VSeqSort l).
Hypothesis Pv_vlt : forall e, Pe e -> forall p, Pv (VLT e p).

Hypothesis Pm_bool : Pm SBool.
Hypothesis Pm_nat : Pm SNat.
Hypothesis Pm_sgtype : forall g : gType, Pg g -> Pm (SGType g).

Hypothesis Pe_var : forall n : nat, Pe (EVar n). 
Hypothesis Pe_end : Pe EEnd.
Hypothesis Pe_msg : forall (d : dir) (c : ch) (s : value), Pv s -> forall e : endpoint, Pe e -> Pe (EMsg d c s e).
Hypothesis Pe_branch : forall (d : dir) (c : ch) (l : seq endpoint), P_elist l  -> Pe (EBranch d c l).
Hypothesis Pe_rec : forall e : endpoint, Pe e -> forall n, Pe (ERec n e).

Hypothesis P_glist_0 : P_glist nil.
Hypothesis P_glist_cons : forall g, Pg g -> forall l, P_glist l -> P_glist (g::l).

Hypothesis P_elist_0 : P_elist nil.
Hypothesis P_elist_cons : forall e, Pe e -> forall l, P_elist l -> P_elist (e::l).

Hypothesis P_mlist_0 : P_mlist nil.
Hypothesis P_mlist_cons : forall s, Pm s -> forall l, P_mlist l -> P_mlist (s::l).

(*Maybe used derive mutual induct instead*) 
Fixpoint gType_rect g : Pg g :=
  let fix seq_gType_rect gs : P_glist gs := 
    match gs with 
     | [::] => P_glist_0
     | g'::gs' => P_glist_cons (gType_rect g') (seq_gType_rect gs') 
     end in
  match g with 
   | GVar n => Pg_var n
   | GEnd => Pg_end
   | GRec n g => Pg_rec (gType_rect g) n
   | GMsg a u g => Pg_msg a (value_rect u) (gType_rect g)
   | GBranch a l => Pg_branch a (seq_gType_rect l)
   end
with mysort_rect m : Pm m :=
match m with 
| SBool => Pm_bool
| SNat => Pm_nat
| SGType g => Pm_sgtype (gType_rect g)
end
with value_rect v : Pv v :=
let fix seq_mysort_rect ss : P_mlist ss :=
 match ss with
  | [::] => P_mlist_0
  | m::ms => P_mlist_cons (mysort_rect m) (seq_mysort_rect ms)
 end
in
match v with 
| VSeqSort ss => Pv_vst (seq_mysort_rect ss)
| VLT e p => Pv_vlt (endpoint_rect e) p
end

with endpoint_rect e : Pe e :=
let fix seq_endpoint_rect ss : P_elist ss :=
 match ss with
  | [::] => P_elist_0
  | m::ms => P_elist_cons (endpoint_rect m) (seq_endpoint_rect ms)
 end in
match e with
| EVar n => Pe_var n
| EEnd => Pe_end
| EMsg d c m e => Pe_msg d c (value_rect m) (endpoint_rect e)
| EBranch d c es => Pe_branch d c (seq_endpoint_rect es)
| ERec n e => Pe_rec  (endpoint_rect e) n
end.



Definition seq_gType_rect : forall gs, P_glist gs :=
 fix seq_gType_rect gs : P_glist gs := 
    match gs with 
     | [::] => P_glist_0
     | g'::gs' => P_glist_cons (gType_rect g') (seq_gType_rect gs') 
     end.

Definition seq_mysort_rect : forall ms, P_mlist ms :=
 fix seq_mysort_rect ss : P_mlist ss :=
 match ss with
  | [::] => P_mlist_0
  | m::ms => P_mlist_cons (mysort_rect m) (seq_mysort_rect ms)
 end.

Definition seq_endpoint_rect : forall es, P_elist es :=
fix seq_endpoint_rect ss : P_elist ss :=
 match ss with
  | [::] => P_elist_0
  | m::ms => P_elist_cons (endpoint_rect m) (seq_endpoint_rect ms)
 end.

End Elimination.


Combined Scheme mut_ind_aux from gType_rect, mysort_rect, value_rect, endpoint_rect.


Section SpecializeElimination. 
Variables (Pg : gType -> Prop) 
          (Pv : value -> Prop) 
          (Pe : endpoint -> Prop) 
          (Ps : mysort -> Prop).

Definition mut_ind := (@mut_ind_aux Pg Pv Pe Ps (Forall Pg) (Forall Pe) (Forall Ps)).  
(*(fun gl => forall g, In g gl ->Pg g)
                                                (fun el => forall e, In e el ->Pe e)
                                                (fun sl  => forall s, In s sl ->Ps s)). *)

Definition true_pred A := fun (_ : A) => nat.
Definition gType_rect_true := (@gType_rect Pg  (@true_pred value) (@true_pred endpoint) (@true_pred mysort) (fun gl => forall g, In g gl ->Pg g)
                                                (@true_pred (seq endpoint))
                                                (@true_pred (seq mysort))).
Check endpoint_rect.
Definition endpoint_rect_true := (@endpoint_rect (@true_pred gType) (@true_pred value) Pe (@true_pred mysort) (@true_pred (seq gType))
                                                (fun el => forall e, In e el -> Pe e)
                                                (@true_pred (seq mysort))).
End SpecializeElimination.



Fixpoint gType_eqb (g0 g1 : gType) { struct g0} : bool :=
let list_eq := fix list_eq s1 s2 {struct s1} := 
                                 match s1,s2 with
                                  | [::] , [::] => true 
                                  | x1 :: s1', x2 :: s2' =>  gType_eqb x1 x2 && (list_eq s1' s2') 
                                  | _ , _ => false 
                                  end
in
match g0, g1 with
| GMsg a0 v0 g0', GMsg a0' v0' g1' => (a0 == a0') && value_eqb v0 v0' && (gType_eqb g0' g1') 
| GRec n g0', GRec n1 g1' => (n == n1) && gType_eqb g0' g1' 
| GEnd, GEnd => true
| GBranch a gs, GBranch a' gs' => (a == a') && (list_eq  gs gs')
| GVar n, GVar n' => n == n'
| _, _ => false
end
with value_eqb (v0 v1 : value) {struct v0} :=
let list_eq := fix list_eq s1 s2 {struct s1} := 
                                 match s1,s2 with
                                  | [::] , [::] => true 
                                  | x1 :: s1', x2 :: s2' => mysort_eqb x1 x2 && (list_eq s1' s2') 
                                  | _ , _ => false 
                                  end
in
match v0, v1 with 
| VSeqSort s0, VSeqSort s1 => list_eq s0 s1
| VLT e0 p0, VLT e1 p1 => endpoint_eqb e0 e1 && ( p0 == p1)
| _ , _ => false
end 

with endpoint_eqb (e0 e1 : endpoint) {struct e0} :=
let list_eq := fix list_eq s1 s2 {struct s1} := 
                                 match s1,s2 with
                                  | [::] , [::] => true 
                                  | x1 :: s1', x2 :: s2' => endpoint_eqb x1 x2 && (list_eq s1' s2') 
                                  | _ , _ => false 
                                  end
in
match e0, e1 with
| EVar n0, EVar n1 => n0 == n1
| EEnd , EEnd => true
| EMsg d ch0 s0 e0, EMsg d1 ch1 s1 e1 =>  (d == d1) && (ch0 == ch1) && (value_eqb s0 s1) && (endpoint_eqb e0 e1)
| EBranch d0 ch0 s0, EBranch d1 ch1 s1 => (d0 == d1) && (ch0 == ch1) && (list_eq s0 s1)
| ERec n0 e0, ERec n1 e1 => (n0 == n1) && endpoint_eqb e0 e1
| _ , _ => false
end
with mysort_eqb (st0 st1 : mysort) {struct st0} :=
match st0,st1 with 
 | SBool, SBool => true
 | SNat, SNat => true
 | SGType g0, SGType g1 => gType_eqb g0 g1
 | _ , _ => false
end.


Ltac case_filter :=  case;try (rewrite /= ; constructor ; done);intros.
Ltac case_filter_on x :=  move : x;case_filter.

Ltac inject :=  split; [ by move=>-> | by case ].
Ltac inject2 :=  split;[ case; by move =>->-> | case;by move =>->-> ]. 
Ltac inject3 := split; [ case;  move=>->; case; move=>->->; done |  case; move =>->->->; done]. 

Locate in_eq. 
Lemma refl_eqbs :  reflexive gType_eqb * (reflexive mysort_eqb * (reflexive value_eqb * (reflexive endpoint_eqb))). 
Proof. unfold reflexive. 
apply : mut_ind; intros;rewrite /= ?eqxx /=; 
       try solve [by rewrite /= | by rewrite H H0 | by rewrite H | induction l; first done; last (inversion H; rewrite H2 /=; auto)| constructor; auto].  
Defined.



Definition reflect_pred A (r : A -> A -> bool) := fun x => forall y, reflect ( x = y) (r x y).
Definition tp A (n : A) :=  True. Check (reflect_pred gType_eqb).
Ltac inject_refl := match goal with [ |- reflect (?f ?n = ?f ?n') _ ] => apply (@equivP (n = n')) end; last (try inject).
Ltac inject_refl2 := match goal with [ |- reflect (?f ?n0 ?n1 = ?f ?n0' ?n1') _ ] => apply (@equivP (n0 = n0' /\ n1 = n1')) end; last (try inject2).

Ltac inject_refl3 := match goal with [ |- reflect (?f ?n0 ?n1 ?n2 = ?f ?n0' ?n1' ?n2') _ ] => apply (@equivP (n0 = n0' /\ n1 = n1' /\ n2 = n2')) end; last (try inject3).

Lemma reflect_and : forall p0 p1 b0 b1, reflect p0 b0 -> reflect p1 b1 ->  reflect (p0 /\ p1) (b0 && b1).
Proof.
intros. inversion H;inversion H0; rewrite /=. constructor. auto. 
constructor. case. intros. auto. constructor. case. intros. done. constructor.  
case. intros. done.
Qed.

Definition list_eq {A} (r : A -> A -> bool) l0 l1 :=  (fix list_eq
     (s1 s2 : seq A) {struct s1} :
       bool :=
     match s1 with
     | [::] =>
         match s2 with
         | [::] => true
         | _ :: _ => false
         end
     | x1 :: s1' =>
         match s2 with
         | [::] => false
         | x2 :: s2' =>
             r x1 x2 &&
             list_eq s1' s2'
         end
     end) l0 l1.


(*Lemma list_eqb_i_eq A (r : A -> A -> bool) l :  (forall g : A,
        In g l ->
        forall g1 : A,
        r g g1 <-> g = g1) -> forall l1, list_eq r l l1 <-> l = l1. 
Proof.
rewrite /list_eq . elim : l. move => H.
case. done. done. 

move => a2 l IH H2 []. done. split. move/andP=>[]. intros. simpl in *. f_equal; auto. apply/H2. auto. auto. 
apply/IH. auto. auto. case. 
move=>->->. apply/andP. split. simpl in H2. move : (H2move => a l0 /andP []. intros. simpl in H2. f_equal;auto. 
Qed.*)

Ltac eqbr := rewrite /= refl_eqbs ; try done.

Definition leib_eq (A : Type) (f : A -> A -> bool) := forall a b, f a b <-> a = b.
Ltac inj := split; solve [ by move/eqP=>-> | by case; move=>->].
Lemma axioms_eqbs : leib_eq gType_eqb *  (leib_eq mysort_eqb *  (leib_eq value_eqb *  leib_eq endpoint_eqb)).
Proof. unfold leib_eq.  apply : mut_ind. 
- intro. case_filter. intros. rewrite /=. inj.
- case_filter.
- intros g IH. case_filter.  rewrite /=. destruct b. split;done. split;done.   split. 
Admitted.
(*
- intros. case_filter_on b. rewrite /=. split.  
 * move/andP => [] /andP => [] [] /eqP=>->.  rewrite H H0. by move =>->->. 
 * case. move =>->->->. by rewrite eqxx /= !refl_eqbs. 
- intros. case_filter_on b. rewrite /=. split. 
 * move/andP=> [] /eqP=>->. intros. f_equal. generalize dependent l0.
   move : H. induction l. move => H. case_filter. done. 
   move => H. case_filter. done. 
   move : b. move/andP. case. intros. inversion H. subst. f_equal. by  rewrite -H2.   apply IHl. 
   done.  apply b. 
 * case. move=>->->. rewrite eqxx /=.  generalize dependent l0.
   case_filter. rewrite refl_eqbs /=.  induction l0. done. 
   rewrite refl_eqbs /=. done. 
- intros. case_filter_on b. rewrite /=. split. 
 * intros. f_equal. generalize dependent l0. induction l.
  ** case_filter. done.
  ** case_filter. done. 
     move : H0. move/andP. case. intros. inversion H. subst. f_equal. 
     apply/H2. done. auto.
 * case. move =>->. induction l0. done. rewrite refl_eqbs /=. apply IHl0. 
- intros. case_filter_on b. destruct p0. rewrite /=. split. 
 * move/andP. case. rewrite H. move =>-> /eqP =>->. done. 
 * case.  move=>->->. by rewrite eqxx refl_eqbs. 
- intros. case_filter_on b. 
- intro. case_filter_on b. 
- intros. move : b. case_filter. rewrite /=. split. 
 * by move/H=>->. case. move=>->. apply refl_eqbs.
- intros. move : b. case_filter. rewrite /=.  split. 
 * by move/eqP=>->. 
 * case. by move=>->. 
- case; rewrite/=; try done. 
- move => d c s IH e. destruct b; rewrite/=; try done. split. 
 by move/andP =>[] /andP [] /andP [] /eqP -> /eqP -> /IH -> /H ->.  
  case. move=>->->->->. by rewrite !eqxx !refl_eqbs. 
(*- intros. case_filter_on b.  rewrite /=. split. 
 * move/andP=>[] /andP [] /eqP -> /H -> /H0 ->. done. 
   case. move=>->->->. by rewrite eqxx !refl_eqbs.*)

- intros. case_filter_on b.  rewrite /=. split. 
  * move/andP=>[] /andP [] /eqP -> /eqP ->. intros. f_equal.
   elim : l l0 H b. case;done. 
   intros. elim : l0 b; first done. intros. move : (andP b) =>[].  intros.
   inversion H0.  subst. f_equal;auto.
   apply/H4. done. 
  * case. move =>->->->. rewrite !eqxx //=.
    elim : l0 H. auto.  rewrite /=. intros. rewrite refl_eqbs //=.
     apply/H. auto. 
(*- intros. case_filter_on b.  rewrite /=. split. 
  * move/andP=>[] /eqP ->. intros. f_equal.
   elim : l l0 H b. case;done. 
   intros. elim : l0 b; first done. intros. move : (andP b) =>[].  intros. inversion H0. f_equal;auto.
   apply/H4. done. auto. 
  * case. move =>->->. rewrite eqxx //=.
    elim : l0 H. auto.  rewrite /=. intros. rewrite refl_eqbs //=.
     apply/H. auto. *)

- intros. case_filter_on b. rewrite /=. rewrite H. split;auto.
  move=>->. done.
  case. done.
all : try (rewrite /=; done).
all : intros;constructor;auto.  
Defined.*)



Lemma iff_reflect : forall A (eqb : A -> A -> bool),
 (forall a0 a1, eqb a0 a1 <-> a0 = a1) -> forall x y , reflect (x = y) (eqb x y).
Proof.
intros. destruct (eqb x y) eqn:Heqn.
- constructor.  rewrite <- H. done. constructor.  intro. specialize H with x y. destruct H. 
  apply H1 in H0. rewrite Heqn in H0. done. 
Qed.

Lemma endpoint_axiom : Equality.axiom endpoint_eqb.
Proof. move : axioms_eqbs. do ? (case;intro). move/iff_reflect. done. 
Qed.

Lemma gType_axiom : Equality.axiom gType_eqb.
Proof. move : axioms_eqbs. do ? (case;intro). move : a.  move/iff_reflect.  done. 
Qed.

Lemma mysort_axiom : Equality.axiom mysort_eqb.
Proof. move : axioms_eqbs. do ? (case;intro). move : a0.  move/iff_reflect.  done. 
Qed.

Lemma value_axiom : Equality.axiom value_eqb.
Proof. move : axioms_eqbs. do ? (case;intro). move : a1.  move/iff_reflect.  done. 
Qed.

Definition endpoint_EqMixin := EqMixin endpoint_axiom.
Canonical endpoint_EqType := EqType endpoint endpoint_EqMixin.

Definition gType_EqMixin := EqMixin gType_axiom.
Canonical gType_EqType := EqType gType gType_EqMixin.

Definition mysort_EqMixin := EqMixin mysort_axiom.
Canonical mysort_EqType := EqType mysort mysort_EqMixin.

Definition value_EqMixin := EqMixin value_axiom.
Canonical value_EqType := EqType value value_EqMixin.




Lemma inP : forall {A : eqType} l (g : A) , reflect (List.In g l) (g \in l).
Proof.
move => A. elim.
rewrite /=. intros. rewrite in_nil. constructor. done.
- move => a l H g. rewrite /=. apply Bool.iff_reflect. split. case.
move=>->. by rewrite in_cons eqxx. rewrite in_cons. move/H=>->.
by rewrite orbC. 
rewrite inE. move/orP =>[].  move/eqP=>->. auto. move/H. auto.
Qed.


Lemma gType_ind
     : forall (Pg : gType -> Prop),
       (forall n : nat, Pg (GVar n)) ->
       Pg GEnd ->
       (forall g : gType, Pg g -> forall n, Pg (GRec n g)) ->
       (forall (a : action) (v : value),
        forall g : gType,
        Pg g -> Pg (GMsg a v g)) ->
       (forall (a : action) (l : seq gType),
         (forall g, g \in l -> Pg g) -> Pg (GBranch a l)) ->
       forall g : gType, Pg g.
Proof.
intros. apply : gType_rect_true;auto.
intros. apply H3. intros. apply H4. by apply/inP. 
all: try (rewrite /true_pred; constructor). 
rewrite /=. done. rewrite /=. 
intros. case : H6. move=><-. auto. auto. 
Qed.

Lemma endpoint_ind
     : forall (Pe : endpoint -> Prop),
       (forall n : nat, Pe (EVar n)) ->
       Pe EEnd ->
       (forall e : endpoint, Pe e -> forall n, Pe (ERec n e)) ->
       (forall d c (v : value),
        forall e : endpoint,
        Pe e  -> Pe (EMsg d c v e)) ->
       (forall d c (l : seq endpoint),
         (forall g, g \in l -> Pe g) -> Pe (EBranch d c l)) ->
       forall g : endpoint, Pe g.
Proof.
intros. apply : endpoint_rect_true;auto.
all: try (rewrite /true_pred; constructor). 
intros.  apply H3. intros. apply H4. by apply/inP. 
rewrite /=. done. rewrite /=. 
intros. case : H6. move=><-. auto. auto. 
Qed.

Section Operations.
Implicit Type g : gType.
(*Fixpoint bound_i (i : nat) g  := 
match g with 
| GEnd => true
| GMsg _ _ g0 => bound_i i g0
| GBranch _ gs => all (bound_i i) gs
(*| GPar g0 g1 => (bound_i i g0) && (bound_i i g1)*)
| GRec g0 => bound_i (S i) g0
| GVar n => n < i
end.

Fixpoint bound_i_e i e := 
  match e with
  | EVar n => n < i
  | EEnd => true
  | ERec g0 => bound_i_e i.+1 g0
  | EMsg _ _ _ g0 => bound_i_e i g0
  | EBranch _ _ gs => all (bound_i_e i) gs
  end.


(*Inspired by Francisco*)
Fixpoint contractive_i (d : nat) g :=
match g with 
| GEnd => true
| GMsg _ _ g0 => contractive_i 0 g0
| GBranch _ gs => all (contractive_i 0) gs
(*| GPar g0 g1 => (contractive_i d g0) && (contractive_i d g1)*)
| GRec g0 => contractive_i (S d) g0
| GVar n => d <= n
end. *)




(*Fixpoint mu_height g :=
match g with
| GRec g0 => (mu_height g0).+1
| _ => 0
end.

Lemma mu_height_subst : forall g0 g1  i, contractive_i (S i) g0 -> mu_height (substitution i g0 g1) = mu_height g0.
Proof. 
elim; try solve [by rewrite /=].
- rewrite /=. intros. case : (eqVneq n i) H. move=>->. by rewrite ltnn. by rewrite /=. 
- intros. rewrite /=. f_equal. apply H. done. 
Qed.




Definition g_next_aux g := 
match g with 
| GMsg a u g0 => Some (a,[::g0])
| GBranch a gs => Some (a,gs)
| _ => None
end.*)


(*Notation dec x := (Sumbool.sumbool_of_bool x).

Equations unf_recs (i : nat) g : gType by wf (mu_height g)  :=
unf_recs i (GRec g) := if (dec (contractive_i i (GRec g))) is left _  then (unf_recs i (substitution i g (GRec g))) else g;
unf_recs i g := g.
Next Obligation.
rewrite mu_height_subst. done. done.
Qed.

Definition g_next g :=
match unf_recs 0 g with 
| GMsg _ _ g0 => [::g0]
| GBranch _ gs => gs
| _ => [::]
end.

Definition act_of_g g :=
match unf_recs 0 g with 
| GMsg a _ _ => Some a
| GBranch a _ => Some a
| _ => None
end.*)

End Operations.
