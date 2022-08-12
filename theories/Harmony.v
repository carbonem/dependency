From mathcomp Require Import all_ssreflect zify.
From Equations Require Import Equations.
From mathcomp Require Import finmap.
From Dep Require Export Linearity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Let inE :=  NewSyntax.inE.

Declare Scope unf_scope.
Locate "+".
Definition unfe e := (e[e ERec e.:  succn >> EVar]). 
Unset Elimination Schemes. 
Inductive Estep : endpoint ->  (dir * ch * (value + nat))  -> endpoint -> Prop :=
| estep_msg d c v e0  : Estep (EMsg d c v e0) (d,c, inl v) e0
| estep_msg_async d vn c c' v e0 e0'  : Estep e0 (d,c,vn) e0' -> c <> c' -> 
                                        Estep (EMsg Sd c' v e0) (d,c,vn) (EMsg Sd c' v e0')
| estep_branch n es d c   :   n < size es -> Estep (EBranch d c es) (d,c, inr n) (nth EEnd es n)
| estep_branch_async es0 es1 vn d c c'  : size es0 = size es1 -> Forall (fun p =>  Estep p.1 (d,c,vn) p.2) (zip es0 es1) -> c <> c' -> Estep (EBranch Sd c' es0) (d,c,vn) (EBranch Sd c' es1)
| estep_rec e l e' : Estep (unfe e) l e' -> Estep (ERec e) l e'.
Set Elimination Schemes.
Hint Constructors Estep.


Lemma Estep_ind
     : forall P : endpoint -> dir * ch * (value + nat) -> endpoint -> Prop,
       (forall (d : dir) (c : ch) (v : value) (e0 : endpoint), P (EMsg d c v e0) (d, c, inl v) e0) ->
       (forall (d : dir) (vn : value + nat) (c c' : ch) (v : value) (e0 e0' : endpoint), 
        Estep e0 (d, c, vn) e0' -> P e0 (d, c, vn) e0' -> c <> c' -> P (EMsg Sd c' v e0) (d, c, vn) (EMsg Sd c' v e0')) ->
       (forall (n : nat) (es : seq endpoint) (d : dir) (c : ch),  n < size es -> P (EBranch d c es) (d, c, inr n) (nth EEnd es n)) ->
       (forall (es0 es1 : seq endpoint) (vn : value + nat ) (d : dir) (c c' : ch),
        size es0 = size es1 ->
        Forall (fun p : endpoint * endpoint => Estep p.1 (d, c, vn) p.2) (zip es0 es1) ->
        Forall (fun p : endpoint * endpoint => P p.1 (d, c, vn) p.2) (zip es0 es1) ->
        c <> c' -> P (EBranch Sd c' es0) (d, c, vn) (EBranch Sd c' es1)) ->
  (*     (forall (e : endpoint) (l : dir * ch * (value + nat) ) (e1 e' : endpoint), epred  e -> epred e1 ->
        ebisimilar e e1 -> P e1 l e' -> P e l e') ->*)
     (forall (e : endpoint) (l : dir * ch * (value + nat) ) ( e' : endpoint), Estep (unfe e) l e' ->
         P (unfe e) l e' -> P (ERec e) l e') ->
       forall (e : endpoint) (p : dir * ch * (value + nat)) (e0 : endpoint), Estep e p e0 -> P e p e0.
Proof.
intros. move : e p e0 H4. fix IH 4;intros. destruct H4.
- apply H;auto.
- apply H0;auto.
- apply H1;auto.
- apply H2;auto. elim : H5;auto. 
- eapply H3; eauto. 
Qed.




Inductive EnvStep : env -> label -> env -> Prop := 
| envstep_rule (Δ Δ' : env) e0 e1 e0' e1' l : Estep e0 (Sd,action_ch l.1,l.2) e0' ->  Estep e1 (Rd,action_ch l.1,l.2) e1' ->  
                           domf Δ = domf Δ' -> (forall p e e',  Δ.[? p] = Some e -> Δ'.[? p] = Some e' -> unfeq e e') -> EnvStep Δ.[ptcp_from l.1 <- e0].[ptcp_to l.1 <- e1] l  Δ'.[ptcp_from l.1 <- e0'].[ptcp_to l.1 <- e1'].
Hint Constructors EnvStep.

Lemma mapf : forall (A : choiceType) (B : Type) (S : {fset A}) (F : A -> B) (k : A), k \in S -> [fmap x : S => F (val x)].[? k] = Some (F k).
Proof.
intros. rewrite /=. rewrite /fnd.  case : insubP;rewrite /=;intros; subst. f_equal. rewrite ffunE. done. rewrite H in i. done. 
Qed.

Lemma mapf2 : forall (A : choiceType) (B : Type) (S : {fset A}) (F : A -> B) (k : A), k \notin S -> [fmap x : S => F (val x)].[? k] = None.
Proof.
intros. rewrite /=. rewrite /fnd.  case : insubP;rewrite /=;intros; subst. rewrite i in H. done. done. 
Qed.

Lemma mapf_if : forall (A : choiceType) (B : Type) (S : {fset A}) (F : A -> B) (k : A),  [fmap x : S => F (val x)].[? k] = if k \in S then Some (F k) else  None.
Proof.
intros. rifliad. rewrite mapf. done. done. rewrite mapf2. done. lia. 
Qed.

Lemma fsubset_in : forall (A : choiceType) (b c : {fset A}), b `<=` c -> (forall j, j \in b -> j \in c).
Proof.
intros. Search _ fsub1set. move : H0. rewrite -!fsub1set.  intros. apply : fsubset_trans. apply : H0. apply H. 
Qed. 






Lemma bool_iff : forall (b0 b1 : bool), b0 = b1 <-> (b0 <-> b1).
Proof. move => [] [];split;auto;intros;try done. suff : false. by  move=>->. by rewrite -H. suff : false. by move=>->. rewrite H. done. 
Qed.






Ltac kb d := let Heqn := fresh "Heqn" in destruct d eqn:Heqn;rewrite ?Heqn //=. 




Lemma ch_diff : forall g a0 aa a1, linear g -> Tr (a0::(aa++[::a1])) g  -> Forall ( fun a => (ptcp_to a) \notin a1) (a0::aa) ->  Forall (fun a => action_ch a != action_ch a1) (a0::aa).
Proof.
intros. apply/List.Forall_forall. intros. 
destruct (eqVneq (action_ch x) (action_ch a1)); last done. inversion H1. subst.
exfalso. simpl in H2. destruct H2. 
- subst. apply : no_indep. apply : H5.  apply H6. move : H.  move/linearP/Linear_1=>HH.  apply : HH. 
  rewrite -[_::_]cat0s in H0. apply : H0. rewrite /same_ch. apply/eqP. done.
- apply List.in_split in H2.  destruct H2,H2. rewrite H2 in H0. move : H. move/linearP=>HH.  rewrite /Linear in HH.
  specialize HH with (a0::x0) x x1 a1. 
have : (a0 :: (x0 ++ (x :: x1)%SEQ)%list ++ [:: a1]) = ((a0 :: x0) ++ x :: x1 ++ [:: a1]).
  rewrite /=. f_equal. rewrite -catA. f_equal.


  intros. move : H0.  rewrite x2. move/HH=>H3. 
  have : same_ch x a1. by rewrite /same_ch e. move/H3. case. intros. move : H1.  
  rewrite H2. intros. inversion H1. apply List.Forall_app in H7. destruct H7. inversion H8. apply : no_indep. 
  apply H11.  apply H12.  done.
Qed.
Open Scope subst_scope.

Lemma size_pred_subst_ren : forall g sigma, size_pred g -> size_pred (g ⟨g sigma⟩).
Proof.  
elim;intros;rewrite /=;simpl in *;try done;auto. split_and. rewrite size_map //=.
rewrite all_map. apply/allP=>g HH.  simpl. apply H. done. apply (allP H2). done.
Qed.

Lemma size_pred_subst : forall g sigma, (forall x, size_pred (sigma x)) -> size_pred g -> size_pred (g[g sigma]).
Proof.  
elim;intros;rewrite /=;simpl in *;try done;auto.
- rifliad. rifliad. simpl. asimpl.   apply H. intros. destruct x. asimpl. done. asimpl. 
apply/size_pred_subst_ren. auto. done.
- rewrite all_map. split_and. rewrite size_map. split_and. apply/allP=> ll Hin /=. apply H. done. split_and. apply (allP H3). done. 
Qed.


Print step.
Lemma step_tr : forall g vn g', step g vn g' -> size_pred g ->  exists s, Tr (s ++ [::vn.1]) g /\ Forall (fun a => (ptcp_to a) \notin vn.1) s.
Proof.
move => g vn g'. elim.
- intros. exists nil. rewrite /=. auto.
- intros. exists nil. rewrite /=. split;auto.  apply TRBranch with (n:=n)(d:=GEnd). done. done.
- intros.  simpl in H2. apply H0 in H2. destruct H2,H2.  exists (a::x). rewrite /=. auto. 
- intros. move : H1.  move/forallzipP=>/=Hall. specialize Hall with GEnd 0.
  have : exists s0 : seq action,
           Tr (s0 ++ [:: l.1]) (nth GEnd gs 0) /\ Forall (fun a : action => ptcp_to a \notin l.1) s0. apply Hall;eauto.
  simpl in H3.  split_and. simpl in H3. split_and. apply (allP H4). apply/mem_nth. done. move => []. intros. exists (a::x). destruct p.  split;auto. simpl. econstructor. 2 : { eauto. }    simpl in H3. split_and. 
- intros.  simpl in H1. eapply size_pred_subst in H1.  apply H0 in H1. destruct H1,H1. exists x. split;auto. case. done. done. 
Qed.


Lemma distinct_ch : forall g vn g', step g vn g' -> size_pred g -> Linear g -> exists s, Tr (s ++ [::vn.1]) g /\  Forall (fun a =>  (action_ch a) != (action_ch vn.1)) s.
Proof. intros. edestruct (step_tr). eauto. done.  destruct H2. exists x. split;auto. inversion H3. done. apply : ch_diff. eauto. subst. eauto. 
auto. 
Qed.

Lemma distinct_ch_msg : forall a u g vn g', step (GMsg a u g) vn g' -> size_pred g -> Linear (GMsg a u g) -> ptcp_to a \notin vn.1 -> (action_ch a) != (action_ch vn.1).
Proof. intros.  edestruct distinct_ch. eauto. done.    done. destruct H3. move : H4. move/Forall_forall=>HH.  destruct x. simpl in *. inversion H3. subst. rewrite !inE in H2. split_and.  apply HH. simpl in H3.  inversion H3. subst. rewrite !inE. done.
Qed.

Lemma distinct_ch_branch : forall a gs vn g', step (GBranch a gs) vn g' -> size_pred (GBranch a gs) -> Linear (GBranch a gs) -> ptcp_to a \notin vn.1 ->  (action_ch a) != (action_ch vn.1).
Proof. intros.  edestruct distinct_ch. eauto. auto. done. destruct H3. move : H4. move/Forall_forall=>HH.  destruct x. simpl in* . inversion H3. subst. rewrite !inE in H2. split_and. simpl in*.  inversion H3. subst. apply HH. rewrite !inE. done.
Qed.

(*
Open Scope nat_scope.
Fixpoint efvg (g : endpoint) : {fset (nat * bool)} := 
match g with 
| EMsg _ _ u g0 => [fset (n,true) | n in endpoint_fv g  (* (fvg g0) *)]
| EBranch _ _ gs  => [fset (n,true) | n in endpoint_fv g (*(\bigcup_(i <- (map fvg gs )) i)*) ] 
| ERec g0  => [fset ((n.1).-1,n.2) | n in (efvg g0) & n.1 != 0]
| EVar n => [fset (n,false)]
| EEnd => fset0
end.

Lemma eguarded_fvg1 : forall g i, eguarded i g -> (i,false) \notin efvg g.  
Proof.
elim;rewrite /=;try done;intros;rewrite ?inE //=.
lia. apply/imfsetP=>[]/= [] x /=. rewrite !inE. split_and. inversion q. 
subst. apply/negP. apply : H. eauto. have : x.1.-1.+1 = x.1 by lia. move=>->.
destruct x.  simpl in *. subst. done. 
apply/imfsetP=>[] [] /= x HH []. done. 
apply/imfsetP=>[] [] /= x HH []. done. 
Qed.

Lemma eguarded_fvg2 : forall g i, ((i,false)  \notin efvg g) -> eguarded i g.
Proof.
elim;rewrite /=;try done;intros.
move : H. rewrite !inE. simpl. lia.
apply H. move : H0.  move/imfsetP=>HH. apply/negP=>HH'. apply/HH. rewrite /=. 
exists (i.+1,false). rewrite !inE. split_and. 
rewrite /=. done. 
Qed.

Lemma guarded_fvg : forall g i, eguarded i g <-> ((i,false) \notin efvg g).  
Proof.
intros. split;intros; auto using eguarded_fvg1, eguarded_fvg2. 
Qed.

Definition injective_for (S : {fset nat}) (f : nat -> nat) := forall n0 n1, n0 \in S -> n1 \in S -> f n0 = f n1 -> n0 = n1. 
*)


Inductive NG : gType -> Prop :=
| NG_end : NG GEnd
| NG_var n : NG (GVar n)
| NG_next g : NG g -> NG (GRec g).
Hint Constructors NG.

Lemma NGP : forall g n, ~ guarded n g -> NG g.
Proof.
elim;intros;auto. 
simpl in *. constructor.   apply: H. eauto. done. done.
Qed. 


Definition no_step g := forall l g', ~ step g l g'.

Definition no_estep g := forall l g', ~ Estep g l g'.

(*Inductive no_step_f  (r : gType -> Prop) : gType -> Prop :=
 | no_step_c g : no_step g -> no_step_f r g
 | no_step2 g: r (g [g (GRec g).:ids]) -> no_step_f r (GRec g).


Notation NoStep := (paco1 no_step_f bot1).  Check paco2.

Lemma no_step_lt : forall g (r1 r2 : gType -> Prop ), (forall g, r1 g -> r2 g) -> no_step_f r1 g -> no_step_f r2 g.
Proof.
intros. inversion H0. subst. constructor. done.  
subst. apply no_step2.  apply H.  done.
Qed. *)


Inductive MUE : endpoint -> Prop :=
| MU_end : MUE EEnd
| MU_mu e : MUE (unfe e)  -> MUE (ERec e).
Hint Constructors MUE. 
Lemma MUE1 : forall e i sigma, ~ eguarded i e -> sigma i = EEnd -> MUE (e [e sigma]).
Proof.
elim;intros; simpl in *. have : n = i. lia. move=>->. rewrite /= H0. done. done.
asimpl. constructor. rewrite /unfe. asimpl. apply : H. eauto. 
asimpl.  rewrite H1. done. 
done.
done.
Qed.



Lemma MUE_no_step : forall e, MUE e -> no_estep e. 
move => e. elim. intro. intros. intro. inversion H. 
intros.  intro. intros. intro. inversion H1.  subst. apply : H0. eauto. 
Qed.


Lemma inject_notin : forall e sigma v, injective sigma ->  v \notin endpoint_fv e -> sigma v \notin endpoint_fv (e ⟨e sigma ⟩). 
Proof.
intros.   suff : sigma v \in endpoint_fv (⟨e sigma ⟩ e) -> v \in endpoint_fv e. 
intros. apply/negP.  intro. apply (negP H0). apply x. apply H1. clear H0. 
elim : e sigma v H;intros;simpl in *. rewrite /= inE in H0. rewrite /= inE.  apply/eqP. apply H. lia. 
rewrite /= inE in H0.  done.
move : H1.  move/imfsetP=> H'.  destruct H'. simpl in *. rewrite /= !inE in H1. split_and. 
apply/imfsetP. exists v.+1. simpl in *. rewrite /= inE.  split_and. destruct x.   done. simpl in *. subst. move : H3.  asimpl. intros. apply : H. instantiate (1 := (0 .: sigma >> succn)).  2 : {    simpl in *. done. } auto. done. apply : H. 2 : { eauto. } done. 
move : H1. rewrite !big_map !big_exists. move/hasP=>HH. destruct HH. apply/hasP. exists x. done. apply : H. done. 2 : { eauto.  }  done. 
Qed.




Lemma inotine2 : forall g i sigma, (forall n, i \notin  endpoint_fv (sigma n)) -> i \notin endpoint_fv g [e sigma].
Proof.
elim;rewrite /=;try done;intros. 
apply/imfsetP=>/=H'. destruct H'. rewrite !inE in H1.  destruct (andP H1). move : H3. asimpl. intros. apply/negP. apply : H. 2 : { apply : H3. } case. simpl. rewrite /= inE. lia. simpl. intros. asimpl. subst. specialize H0  with n.   apply (@inject_notin _ (succn)) in H0.  destruct x. done. simpl in *. apply H0. 
done.
rewrite !big_map !big_exists. apply/negP. move/hasP=>HH. destruct HH. apply/negP. apply : H. eauto. eauto. done. 
Qed.


Lemma econtractive2_ren : forall g sigma, injective sigma -> (forall n, n <= sigma n) ->  econtractive2  g -> econtractive2 g ⟨e sigma ⟩.
Proof.
elim;intros;simpl;try done. 
asimpl. split_and. have : 0 = ( 0 .: sigma >> succn) 0. done. intros. rewrite {1}x.

rewrite -eguarded_shift. simpl in H2. split_and. auto.
apply H. auto.  case. done. done.  simpl in H2. split_and. apply H.  done. done. done.
rewrite all_map. apply/allP. intro. intros. simpl. apply H. done.  done. done.  simpl in H2. apply (allP H2). done.
Qed.


Lemma econtractive2_subst : forall g sigma, econtractive2 g -> (forall n, econtractive2 (sigma n)) -> econtractive2 g [e sigma].
Proof. 
elim;rewrite /=;intros;try done. 
asimpl. split_and. 
apply/eguarded_sig2.
instantiate (1 := (EVar 0 .: (ids >>  ⟨e ↑ ⟩))).  asimpl. done.
case. done. simpl. intros. apply/eguarded_fv. asimpl. apply/inotine. done.
apply H. done.  intros. destruct n.  done. simpl. asimpl.  apply/econtractive2_ren. done. done. done.
apply H. done.  intros. done. 
rewrite all_map. apply/allP. intro. intros. simpl. apply H. done. apply (allP H0). done. done.
Qed.


Lemma cont_project : forall g p, econtractive2 (project g p).
Proof.
elim;rewrite //=;intros. 
- case_if.  
  * simpl. split_and. simpl. split_and. 
- rifliad; try done. 
  simpl. 
  done. 
  simpl. 
  done. 
- rifliad.  
  simpl. rewrite all_map.  
  apply/allP. 
  intro. intros. 
  simpl. 
  apply H. 
  done.


  simpl. rewrite all_map.  
  apply/allP. 
  intro. intros. 
  simpl. 
  apply H. 
  done.

destruct l.  
done. 

apply H. 
rewrite inE eqxx. done. 
Qed. 


Lemma fv_lt : forall g p n, n \in (endpoint_fv (project g p)) -> n \in (gType_fv g).
Proof. 
elim. 
intros. 
move : H. 
rewrite /= inE. 
done.

intros. 
move : H. 
rewrite /= inE. 
done.

intros. 
move : H0. 
rewrite /= ?inE. 
case_if; intros.  
apply/imfsetP. 
simpl in *. 
move : H1. move/imfsetP. 
move=>[]. 
simpl. 
intros. 
exists n.+1.
rewrite !inE /=. 
split_and. 
subst. 
rewrite !inE /= in p0. 
split_and. 
destruct x. 
done. 
simpl. 
apply : H. 
apply : H1. 
lia. 
simpl in *. rewrite /= inE in H1. done. 
intros. 
move : H0. 
rewrite /=. 
rifliad. 
rewrite /= ?inE. 
move/H. 
eauto. 

rewrite /= ?inE. 
move/H.  
done. 
move/H. 
done. 

intros. 

move : H0. 
rewrite /=. 
rifliad; simpl.  
all : rewrite !big_map. 
all : rewrite !big_exists. 
move/hasP=>[]. intros.  
apply/hasP.
exists x.  
done. 
apply : H. 
done. 
apply : q. 
move/hasP=> []. intros.  
apply/hasP. 
exists x. 
done. 
apply : H. 
done. 
apply : q. 
destruct l. 
rewrite inE. 
done. 
intros. 

simpl.
apply/orP. 
left. 
apply/H. 
auto. 
apply : H2. 
Qed. 

Lemma bound_proj : forall g p i, bound_i i g -> ebound_i i (project g p). 
Proof.
elim;intros.   
rewrite /=.
rewrite /= in H. 
done.
done.
rewrite /=.
rewrite /= in H0. 
case_if. 
rewrite /=.
apply H. 
done.
done.
simpl in *.
rifliad; rewrite //=.
apply H. 
done.
apply H.
done.
apply H.
done.
simpl in *. 
rifliad; rewrite /=.  
rewrite /= all_map. 
apply/allP. intro. 
intros. 
rewrite /=.
apply H. 
done.
apply (allP H0). 
done.
rewrite /= all_map. 
apply/allP. 
intro. 
intros.
rewrite /=.
apply H.
done.
apply (allP H0). 
done.
destruct l. 
done.
apply H. 
done.
simpl in *.
split_and. 
Qed. 

Lemma spred_proj : forall g p, size_pred g -> esize_pred (project g p). 
Proof.
elim;intros. 
rewrite /=. 
done.
done.
rewrite /=. 
case_if. 
rewrite /=. 
simpl in H0. 
auto. 
done. 
rewrite /=. 
rifliad. 
rewrite /=. 
apply H. 
rewrite /= in H0. 
done. 
rewrite /=. 
apply H. 
rewrite /= in H0. 
done.
apply H. 
done.
rewrite /=. 
rifliad. 
rewrite /=. 
split_and. 
rewrite /= size_map. 
rewrite /= in H0. 
split_and.
rewrite /= all_map. 
apply/allP. 
intro. 
intros. 
rewrite /=. 
apply H. 
apply H2. 
rewrite /= in H0. 
split_and.
apply : (allP H4). 
done.
rewrite /=.
split_and.
rewrite /= size_map. 
rewrite /= in H0. split_and. 
rewrite /= all_map. 
apply/allP. 
intro. 
intros.
rewrite /=. 
apply H. 
done. 
rewrite /= in H0. 
split_and.
apply (allP H5). 
done.
destruct l. 
done.
apply H. 
done.
rewrite /= in H0. 
split_and.
Qed. 








Lemma big_fset0 : forall gs g, g \in gs -> \bigcup_(j <- gs) gType_fv j = fset0 -> gType_fv g = fset0. 
Proof.
intros.
move : H0. move/fsetP=> HH. 
apply/fsetP=> k.  apply Bool.eq_true_iff_eq. 
split. 
rewrite /= -HH.  intros. rewrite /= big_exists. apply/hasP. 
exists g. done. done.  
rewrite /= inE. done.
Qed. 

(*Lemma step_cont : forall g l g', step g l g' -> contractive2 g.
Proof.
move => g l g'. elim;intros.
simpl in *. unlock gpred in H. simpl in *. split_and. 
simpl in *. unlock gpred in H. simpl in *. split_and. 
simpl in *. unlock gpred in H. simpl in *. split_and. 
simpl in *. unlock gpred in H. simpl in *. split_and. 
simpl in *. unlock gpred in H. simpl in *. split_and. 
Qed. *)




Definition preds (A : eqType) (l : seq (pred A)) : pred A := (foldr predI predT l).

Definition lpreds := locked preds.


Notation gpred := (lpreds (linear::size_pred::nil)). 
Notation epred := (lpreds (econtractive2::esize_pred::nil)).

(*Lemma bound_subst : forall g sigma i, (forall v, v \in gType_fv g -> bound_i i (sigma v)) -> bound_i i (g [g sigma]).
Proof.
elim;intros;simpl in *. apply H.  rewrite !inE. auto. 
done. 
asimpl. apply H.  intros. *)


Lemma linear_sgmsg : forall a u g0, Linear (GMsg a u g0) -> Linear g0.
Proof. 
move => a u g0. rewrite /Linear /=.  intros. move : (H (a::aa_p) a0 aa a1). rewrite cat_cons /=. 
  destruct ( aa_p ++ a0 :: rcons aa a1) eqn:Heqn. case : aa_p H0 Heqn.  done. done.
  intros. have : Tr ((a::aa_p ++ (a0::aa) ++ [::a1])) (GMsg a u g0). auto.  move/H2 => H3.  move : (H3 H1). 
  move => [] mi [] mo. intros. auto. 
Qed.
Check Forall. 
Lemma linear_branch_aux : forall a gs, Linear (GBranch a gs) -> Forall Linear gs.  
Proof.
move => a gs. intros. apply/List.Forall_forall. intros. rewrite /Linear. intros. unfold Linear in H. have : Tr (a::aa_p ++ a0::aa ++ ([::a1])) (GBranch a gs). move : H0.  move/In_in. move/nthP=>Hnth. specialize Hnth with GEnd. destruct Hnth. rewrite -H3 in H1. apply : TRBranch. eauto. apply : H1. 
intros. apply : H. rewrite -cat_cons in x0. apply : x0. done. 
Qed.


Lemma linear_branch : forall a gs n, Linear (GBranch a gs) -> n < size gs -> Linear (nth GEnd gs n).
Proof. intros. apply linear_branch_aux in H. move : H. move/Forall_forall=> HH.  intros. apply HH.  apply/mem_nth. done. 
Qed. 

Hint Resolve mem_nth.

Lemma linear_unf : forall g, Linear (GRec g) ->  Linear (unfg g).
Proof.  
move => g. rewrite /Linear. move => HH aap a0 aa a1 H0 H1.  apply : HH. constructor. eauto. done. 
Qed.

Lemma step_test : forall g l g', step g l g' -> Linear g /\ size_pred g -> 
Estep (project g (ptcp_from l.1)) (Sd,action_ch l.1,l.2) (project g' (ptcp_from l.1)).
Proof. move => g l g'. elim.
- intros. rewrite /= eqxx. constructor.

- intros. rewrite /= ?eqxx. erewrite <- (@nth_map _ _ _ EEnd (fun g => project g (ptcp_from a))).    apply estep_branch.
  rewrite size_map.  done.  done.  

- intros. move : H2. intros. rewrite !inE in H1.  
  rewrite /=. split_and. rewrite [_ == ptcp_to a]eq_sym. rewrite (negbTE H3).
  rifliad.
 * constructor. 
  * apply H0. move : H2. rewrite /=. split_and. Check linear_sgmsg. apply : linear_sgmsg. eauto. 
    apply/eqP. rewrite neg_sym.  apply : distinct_ch_msg. apply : GR3.   eauto. rewrite !inE. split_and. 
    move : H2. rewrite /gpred.  unlock preds. rewrite /=. split_and.
    move : H2. rewrite /gpred.  unlock preds. rewrite /=. split_and.
    apply/linearP.  eauto. rewrite !inE. split_and.
    apply H0. 
    move : H2. rewrite /gpred.  unlock preds. rewrite /=. split_and. 
    split_and. apply : linear_sgmsg. eauto. 
(*use size and linear assumption*)
- intros. rewrite /=. rewrite !inE in H2. split_and. rewrite eq_sym. rifliad.
 * constructor.
  * rewrite !size_map.  done. 
  * apply/forallzipP. rewrite !size_map.  done. intros. simpl. rewrite size_map in H7.  repeat erewrite nth_map.  move : H1. move/forallzipP. simpl. move => HH. 
    apply : HH. done.  done.  split_and. apply : linear_branch.  eauto. done. simpl in *. split_and. 
    apply (allP H8). apply/mem_nth. done. 
    rewrite -H. auto. auto.
    apply/eqP. rewrite neg_sym.  apply : distinct_ch_branch.  eauto. apply GR4. apply H. done.  rewrite !inE. split_and. 
    move : H3. rewrite /gpred.  unlock preds. simpl. split_and.
    apply/linearP.   move : H3. rewrite /gpred.  unlock preds. simpl. split_and.
    rewrite !inE.  split_and. 
 * move : H7. move/eqP=> HH. rewrite HH eqxx in H4.  done. 
 * rewrite !match_n.  move : H1. move/forallzipP. simpl. move => HH. apply HH.   done. simpl in *.   split_and. 
  split_and. apply linear_branch_aux in H2. move : H2. move/Forall_forall => HH2.  intros. apply HH2. apply/mem_nth.  simpl in *. split_and. 
  simpl in *. split_and.  apply (allP H8). auto. 

- intros. simpl in *. case_if. constructor. have :  Linear (unfg g0) /\ size_pred (unfg g0). split. apply/linear_unf. split_and.  
  apply size_pred_subst. case. simpl. split_and. done. split_and. move/H0. rewrite project_subst /unfe.

have : (project g0 (ptcp_from l0.1))[(GRec g0 .:  succn >> var) >> project^~ (ptcp_from l0.1)] =
 ([e(ERec (project g0 (ptcp_from l0.1))).: succn >> EVar] (project g0 (ptcp_from l0.1))).
asimpl. f_equal. fext. case. asimpl. rewrite /= H2.  done. intros. asimpl. simpl in *. done.
move => ->.  done. move => x0 x1. destruct x0,x1; try done. simpl.  case. move=>->. done. 
rewrite project_subst in H0. move : H0. asimpl. rewrite /= H2. intros. 
have:  [eEEnd .:succn >> (var >> project^~ (ptcp_from l0.1))] = [eEEnd .: succn >> ids]. fext. case;try done. intros. 
rewrite x in H0. 

clear x.   exfalso. apply : MUE_no_step. apply : MUE1. have: ~ eguarded 0 (project g0 (ptcp_from l0.1)).  lia. intros. apply : x. 2 : {  eapply H0. split.  apply linear_unf. split_and. apply size_pred_subst.   case. simpl. split_and. done. split_and. } simpl in *. done.
intro. destruct x1,x2;try done.  simpl. case. move=>->. done. 
Grab Existential Variables.
all : repeat constructor. 
Qed.

Locate size_pred.


Ltac ssa := simpl in *; split_and;try done.
Lemma action_pred_ren : forall g sigma, action_pred g -> action_pred (g ⟨g sigma⟩).
Proof.  
elim;intros;rewrite /=.  done. done. asimpl. apply H. done. ssa. ssa. 
rewrite all_map. apply/allP. intro.  intros. simpl.  apply H. done. apply (allP H2). done. 
Qed. 

Lemma action_pred_subst : forall g sigma, (forall v, action_pred (sigma v)) ->  action_pred g -> action_pred (g [g sigma]).
Proof.  
elim;intros;rewrite /=.  done. done. asimpl. apply H. case. done. intros. simpl. asimpl.  auto. 
apply action_pred_ren. done.  done. ssa.  ssa.
rewrite all_map. apply/allP. intro.  intros. simpl.  apply H. done.  done. apply (allP H3). done. 
Qed.


Lemma step_test2 : forall g l g', step g l g' -> Linear g /\ size_pred g /\ action_pred g -> 
Estep (project g (ptcp_to l.1)) (Rd,action_ch l.1,l.2) (project g' (ptcp_to l.1)).
Proof. move => g l g'. elim.
- intros. rewrite /= eqxx. case_if. split_and. simpl in *. split_and.  rewrite eq_sym H0 in H3. done. constructor. 

- intros. rewrite /= ?eqxx. erewrite <- (@nth_map _ _ _ EEnd (fun g => project g (ptcp_to a))).  

  case_if. simpl in *. split_and. rewrite eq_sym H1 in H4. done.

  apply estep_branch.
  rewrite size_map.  done.  done.  

- intros. move : H2. intros. rewrite !inE in H1.  
  rewrite /=. split_and. rewrite [_ == ptcp_to a]eq_sym. rewrite (negbTE H4).
  rifliad.
 * constructor. 
  * apply H0. simpl in *. split_and. apply : linear_sgmsg. eauto. 
    apply/eqP. rewrite neg_sym.  apply : distinct_ch_msg. apply : GR3.   eauto. rewrite !inE. split_and. 
    move : H2.  rewrite //=. eauto.  
    rewrite !inE. split_and. 
    apply H0. split_and.
    apply : linear_sgmsg.  eauto. 
    move : H5.  rewrite //=. 
    split_and. 

- intros. rewrite /=. rewrite !inE in H2. split_and. rewrite eq_sym. rifliad.
 * constructor.
  * rewrite !size_map.  done. 
  * apply/forallzipP. rewrite !size_map.  done. intros. simpl. rewrite size_map in H8.  repeat erewrite nth_map.  move : H1. move/forallzipP. simpl. move => HH. 
    apply : HH. done.  done.  split_and. apply : linear_branch.  eauto. done. simpl in *. split_and. 
    apply (allP H10). apply/mem_nth. done.
    ssa. apply (allP H9). auto. rewrite -H.  done.  done. 
    apply/eqP. rewrite neg_sym.  apply : distinct_ch_branch.  eauto. apply GR4. apply H. done.  rewrite !inE. split_and.  ssa. ssa.
    rewrite !inE.  ssa. 
 * move : H8. move/eqP=> HH. rewrite HH eqxx in H5.  done. 
 * rewrite !match_n.  move : H1. move/forallzipP. simpl. move => HH. apply HH.   done. simpl in *.   split_and. 
  split_and. apply linear_branch_aux in H2. move : H2. move/Forall_forall => HH2.  intros. apply HH2. apply/mem_nth.  simpl in *. split_and. 
  simpl in *. split_and.  apply (allP H10). auto. ssa. apply (allP H9).  auto. 

- intros. simpl in *. auto. case_if. constructor. have :  Linear (unfg g0) /\ size_pred (unfg g0) /\ action_pred (unfg g0). split. apply/linear_unf. split_and.  
  ssa.  apply size_pred_subst. case. simpl. done. split_and. done. Locate size_pred_subst. apply action_pred_subst. case. done. done. done. move/H0. rewrite project_subst /unfe.

have : (project g0 (ptcp_to l0.1))[(GRec g0 .:  succn >> var) >> project^~ (ptcp_to l0.1)] =
 ([e(ERec (project g0 (ptcp_to l0.1))).: succn >> EVar] (project g0 (ptcp_to l0.1))).
asimpl. f_equal. fext. case. asimpl. rewrite /= H2.  done. intros. asimpl. simpl in *. done.
move => ->.  done. move => x0 x1. destruct x0,x1; try done. simpl.  case. move=>->. done. 
rewrite project_subst in H0. move : H0. asimpl. rewrite /= H2. intros. 
have:  [eEEnd .:succn >> (var >> project^~ (ptcp_to l0.1))] = [eEEnd .: succn >> ids]. fext. case;try done. intros. 
rewrite x in H0. 

clear x.   exfalso. apply : MUE_no_step. apply : MUE1. have: ~ eguarded 0 (project g0 (ptcp_to l0.1)).  lia. intros. apply : x. 2 : {  eapply H0. split.  apply linear_unf. split_and. ssa. apply size_pred_subst.   case. simpl. split_and. done. split_and. 
apply action_pred_subst. case.  done.  done.  done. }
 simpl in *. done.
intro. destruct x1,x2;try done.  simpl. case. move=>->. done. 
Grab Existential Variables.
all : repeat constructor. 
Qed.





Lemma unfeq_refl : forall e, econtractive2 e -> unfeq e e.
Proof.
intros. funelim (unfeq e e); try done; try rewrite -Heqcall.  inversion H0. lia. 
inversion H1. subst. rewrite !eqxx /=.  apply H. simpl in *. done. f_equal. done.
inversion H1. subst. rewrite !eqxx /=. clear Heqcall H1. elim : es0 H H0 . simpl in *.  simp foldIn. simpl in *.  
intros. simp foldIn. simpl in *. simp list_eq2. split_and. apply : H0. 4 : {  f_equal.   } auto.  auto. done.  done.  apply H.  

intros.  apply : H0. 4 : {   eauto. }   auto.  auto.  done. done. done.
rewrite /= eqxx. done.
clear Heq.
rewrite  H in e0. done. 
Qed.

(*Lemma unfeq2_refl : forall e, econtractive2 e -> unfeq2 e e.
Proof.
intros. rewrite /unfeq2. rewrite unfeq_refl. done.
done.
Qed. *)





Lemma project_tw0 : forall g p0 p1,size_pred g ->  p0 \notin  g -> p1 \notin g -> project g p0 = project g p1.  
Proof.
elim; rewrite /=;intros;try done. 

erewrite H;eauto.
move : H1 H2.   rewrite /= !inE /=. ssa. 
rewrite (negbTE H1). rewrite (negbTE H7). 
rewrite (negbTE H2). rewrite (negbTE H5).  apply H. eauto.  eauto.  eauto. 
move : H1 H2.   rewrite /= !inE /=. ssa. 
rewrite (negbTE H1). rewrite (negbTE H7). 
rewrite (negbTE H2). rewrite (negbTE H5).  
rewrite !match_n.  apply H. auto. apply (allP H8). apply/mem_nth. done. 
apply/negP.  intro. apply (negP H6). rewrite big_exists. 
rewrite has_map. simpl. 
apply/hasP.  simpl. exists (nth GEnd l 0). apply/mem_nth. done. done. 
apply/negP.  intro. apply (negP H4). rewrite big_exists. 
rewrite has_map. simpl. 
apply/hasP.  simpl. exists (nth GEnd l 0). apply/mem_nth. done. done. 
Qed.




Lemma project_predP_aux : forall a gs p i, project_pred (GBranch a gs) /\ size_pred (GBranch a gs) -> 
p \notin a -> i < size gs  -> unfeq (project (nth GEnd gs 0) p) (project (nth GEnd gs i) p).
Proof. 
intros. ssa.
move : H2. move/allP=>Hall. have : (nth GEnd gs i) \in gs. auto. 
move/Hall=> HH.  rewrite /= big_map in HH.

destruct (p \in (fresh (a `|` \bigcup_(j <- gs) ptcps j) |` (a `|` \bigcup_(j <- gs) ptcps j) `\` a)) eqn : Heqn.
apply (allP HH). done.

 rewrite !(@project_tw0 _ p (fresh (a `|` \bigcup_(j <- gs) ptcps j) )).

apply (allP HH).

rewrite !inE. done. 

apply (allP H4). apply/mem_nth.  done. 
move : Heqn. move/negP/negP. rewrite /= !inE. split_and.  rewrite !inE in H0.  split_and.  rewrite (negbTE H6) (negbTE H7) /= in H2. move : H2. move/bigfcupP=>HH'.  apply/negP. intro. apply HH'. exists (nth GEnd gs i). split_and. done. 

move : Heqn. move/negP/negP. rewrite /= !inE. split_and.  rewrite !inE in H0.  split_and.  rewrite (negbTE H6) (negbTE H7) /= in H2. move : H2. move/bigfcupP=>HH'.  
rewrite /fresh.  destruct (atom_fresh_for_list (([fset ptcp_from a; ptcp_to a] `|` \bigcup_(j <- gs) ptcps j))) eqn : Heqn. 
rewrite Heqn. apply/negP. intro. apply n. rewrite !inE. apply/orP. right. rewrite big_exists. apply/hasP. 
exists (nth GEnd gs i). auto. done.
apply (allP H4). apply/mem_nth.  done. 
move : Heqn. move/negP/negP. rewrite /= !inE. split_and.  rewrite !inE in H0.  split_and.  rewrite (negbTE H6) (negbTE H7) /= in H2. move : H2. move/bigfcupP=>HH'.  apply/negP. intro. apply HH'. exists (nth GEnd gs 0). split_and. done. 
move : Heqn. move/negP/negP. rewrite /= !inE. split_and.  rewrite !inE in H0.  split_and.  rewrite (negbTE H6) (negbTE H7) /= in H2. move : H2. move/bigfcupP=>HH'.  

rewrite /fresh.  destruct (atom_fresh_for_list (([fset ptcp_from a; ptcp_to a] `|` \bigcup_(j <- gs) ptcps j))) eqn : Heqn. 
rewrite Heqn. apply/negP. intro. apply n. rewrite !inE. apply/orP. right. rewrite big_exists. apply/hasP. 
exists (nth GEnd gs 0). auto. done.
Qed.

(*Lemma project_predP_aux2 : forall a gs p i n, lpreds rec_pred (GBranch a gs) ->
p \notin a -> i < size gs  ->  esize (project (nth GEnd gs 0) p) * esize (project (nth GEnd gs i) p) <= n -> unfeq n (project (nth GEnd gs 0) p) (project (nth GEnd gs i) p).
Proof. 
intros.*) 

Lemma unfeq_unf : forall e e', econtractive2 (ERec e) -> unfeq (e [e (ERec e)..]) e' ->
  unfeq (ERec e) e'.
Proof.
intros. funelim (unfeq (ERec e) e');try done. 
rewrite -Heqcall. inversion H2.  subst.  rewrite /= H1.  lia. 
simpl in *. split_and. clear Heq. inversion H1. subst. rewrite /= H2 H3 in e0.
done.
Qed.

(*


Lemma unfeq_unf2 : forall e e', econtractive2 (ERec e) ->  unfeq (ERec e) e' -> unfeq (e [e (ERec e)..]) e'.
Proof.
intros. funelim (unfeq (ERec e) e');try done. 
inversion H2. subst. rewrite /= Heqcall.   done. 
simpl in *. split_and. clear Heq. inversion H1. subst. rewrite /= H2 H3 in e0.
done.

inversion H2. subst. rewrite /= Heqcall.   done. 
simpl in *. split_and. clear Heq. inversion H1. subst. rewrite /= H2 H3 in e0.
done.


inversion H2. subst. rewrite /= Heqcall.   done. 
simpl in *. split_and. clear Heq. inversion H1. subst. rewrite /= H2 H3 in e1.
done.


inversion H2. subst. rewrite /= Heqcall.   done. 
simpl in *. split_and. clear Heq. inversion H1. subst. rewrite /= H2 H3 in e0.
done.

inversion H3. subst. rewrite -Heqcall in H2. apply H.  
done. rewrite /= -Heqcall.  done. 
f_equal.
funelim (unfeq (ERec e0) (ERec e1'));try done.  rewrite /= -Heqcall0.

 simp unfeq.
funelim (unfeq_unfold_clause_5 e0 (Sumbool.sumbool_of_bool (econtractive2 (ERec e0))) e1').
  have : econtractive2 (ERec e0) = true.  done. intros.
(*edestruct (econtractive2 (ERec e0)).*)
 Set Printing All. 
rewrite /Sumbool.sumbool_of_bool. 
rewrite x.  Set Printing All. setoid_rewrite x.move=>->.

setoid_rewrite H1.

destruct (orP H2). apply H. done.
funelim (unfeq (ERec e0) (ERec e1'));try done. 
  simp unfeq. rewrite /= H1.   simpl in *. simpl in *. done. done. 
simpl in *. split_and. clear Heq. inversion H1. subst. rewrite /= H2 H3 in e0.
done

inv

rewrite Heqcall. inversion H2.  done.  
simpl in *. split_and. clear Heq. inversion H1. subst. rewrite /= H2 H3 in e0.
done.
rewrite -Heqcall. inversion H2.  done.  
simpl in *. split_and. clear Heq. inversion H1. subst. rewrite /= H2 H3 in e1.
done.
rewrite -Heqcall. inversion H2.  done.  
simpl in *. split_and. clear Heq. inversion H1. subst. rewrite /= H2 H3 in e0.
done.
rewrite -Heqcall. inversion H3.  rewrite  H2. lia. 
simpl in *. split_and. clear Heq. inversion H1. subst. rewrite /= H2 H3 in e0.
done.
Qed.*)


(*Lemma step_test_end : forall g l g' p, step g l g' -> project g p = EEnd -> project g' p = EEnd.
Proof.
move => g l g' p. elim. 
- intros. simpl in *. move : H0. case_if.  done. case_if. done. done. 
- intros. simpl in *. move : H1. case_if.  done. case_if. done. rewrite /= match_n. intros.  rewrite /= -H3. symmetry. 
 suff :  unfeq  (project (nth GEnd gs 0) p) (project (nth GEnd gs n) p). rewrite /= H3.
  funelim ( unfeq EEnd (project (nth GEnd gs n) p));try done.
  rewrite /= -Heqcall. done.
 rewrite /= -Heqcall. done.
rewrite /= -Heqcall. done.

rewrite /= -Heqcall. done.

apply : project_predP_aux. unlock lpreds.  rewrite /gpred in H. unlock preds in H. simpl in *. split_and. eauto. done. 
rewrite /= !inE. split_and.  rewrite /= H1. done. rewrite /= H2. done. done. 
- intros. simpl in *. move :H3.  case_if.  done. case_if.  done. done.
- intros. simpl in *. move :H4.   case_if.  done. case_if.  done.  rewrite /= !match_n.  intros. 
  move : H2.  move/forallzipP=>HH. simpl in *. apply : HH.  done. cc. eauto.   

- intros. simpl in *. move : H2. case_if. done. move => _. apply H1. rewrite /= project_subst. asimpl. 
  simpl in *. rewrite /= H2. have : (EEnd .: (var >> project^~ p)) = (EEnd .: ids). fext. case.  done. simpl in *.
  intros.  done. move=>->.  done.

 qqq
rewrite /= -H6.  symmetry.
   suff :  unfeq  (project (nth GEnd gs 0) p) (project (nth GEnd gs n) p). rewrite /= H3.
  funelim ( unfeq EEnd (project (nth GEnd gs n) p));try done.
  rewrite /= -Heqcall. done.
 rewrite /= -Heqcall. done.
rewrite /= -Heqcall. done.

rewrite /= -Heqcall. done.

apply : project_predP_aux. unlock lpreds.  rewrite /gpred in H. unlock preds in H. simpl in *. split_and. eauto. done. 
rewrite /= !inE. split_and.  rewrite /= H1. done. rewrite /= H2. done. done. 

done.
-

lia. 
unloce 
rewrite /= -Heqcall. done.
 simp unfeq. 
 suff : 
Check project_predP_aux.
destruct gs. simpl in *. done. case : n . zdone.
*)

Lemma unfeq_end e : unfeq EEnd e = is_mue e.
Proof.
intros. funelim (unfeq EEnd e);try done. 
Qed. 


Lemma is_mue_fset0 : forall e,  is_mue e -> endpoint_fv e = fset0.
Proof.
elim;intros.
simpl in *. done. 
done.
simpl in *. rewrite /= H. apply/fsetP=>k. 
apply Bool.eq_true_iff_eq. split.  move/imfsetP.  case.  simpl in *. intros. rewrite /= inE in p. done.
rewrite /= inE. done.
done.
simpl in *. done.
simpl in *. done.
Qed.

Lemma subst_fset0 : forall e sigma, (forall n, n \in endpoint_fv e -> sigma n = EVar n) -> e [e sigma] = e.
Proof.
elim;intros;simpl in *. apply H. rewrite /= inE. done. done. 
asimpl.  f_equal. apply H.  case. simpl in *. done. intros. simpl in *. asimpl. 
rewrite /= H0.  simpl in *. done.
apply/imfsetP. simpl in *. exists n.+1. rewrite /= !inE.  split_and. done. 
f_equal. apply H.  done.
f_equal. induction l.  done. simpl in *. f_equal. apply H.  done. intros. apply H0.
rewrite big_cons inE. rewrite /= H1. lia. apply IHl.  intros. apply H. rewrite /= inE H1. lia. done. 
intros. apply H0. rewrite big_cons inE H1.   lia.
Qed.

Lemma is_mue_no_subst : forall e sigma, is_mue e -> e [e sigma] = e.
Proof. intros. apply subst_fset0. intros. rewrite /= is_mue_fset0 in H0. rewrite /= inE in H0.  done.
done.
Qed.


Lemma is_mue1 : forall e0, is_mue e0 -> is_mue ([e(ERec e0)..] e0).
Proof.
intros. rewrite subst_fset0. done.
intros.  rewrite /= is_mue_fset0 in H0.  rewrite /= inE in H0.  done. done.
Qed.

Hint Resolve is_mue1 is_mue_no_subst.

Ltac case_sum := match goal with 
(*                   | [ H : (_ && _) = true  |- _ ] => destruct (andP H);clear H*)
                   |  |- context[Sumbool.sumbool_of_bool ?b ] => destruct  (Sumbool.sumbool_of_bool b )
                  end;simpl in *;try done.

Notation isnt_rec e := (if e is ERec _ then false else true).

Lemma unf_not_rec : forall e0 e1, unfeq (ERec e0) e1 -> isnt_rec e1 -> unfeq (e0 [e (ERec e0)..]) e1.
Proof.
intros. destruct e1; try done.  
move : H. simp unfeq. case_sum.
move : H. simp unfeq. case_sum.
move : H. simp unfeq. case_sum.
move : H. simp unfeq. case_sum.
Qed.

(*Lemma is_mue_unfeq1 : forall e0 e1, is_mue e0 -> unfeq e0 e1 -> unfeq EEnd e1.
roof.
elim;try done;intros.
destruct (isnt_rec e1) eqn :Heqn. apply unf_not_rec in H1;try done. rewrite /= is_mue_no_subst in H1.    apply H.  
 done. done. done. apply H.  done. destruct e1; try done. 
move : H1. simp unfeq. case_sum. 
move/orP.  case.  apply H. done. simpl in *. done. rewrite /= is_mue_no_subst.

rewrite /= unfeq_end.  done. rewrite /= unfeq_end.  done.
simp unfeq. move : H1.  simp unfeq. case_sum. move/orP. case.  intros. 
case_sum.  

case_sum.  /orP.  
one.  done.
move : H1.  simp unfeq. case_sum. move/orP. case. 
Urewrite /= is_mue_fset0 in H1. 
simpl in *. 
rewrite /= subst_fset0 in H1.  apply H.  done. done. intros.  rewrite /= subst_fset0 in H1. 
destruct e1;try done. 

simpl in *. apply H. done. move : H1. intros.   
funelim (unfeq e e1);try done. 
move : H1. simp unfeq . simpl in *. destruct e;try done. simpl in *.
move/orP. case. rewrite /= unfeq_end. done. rewrite /= unfeq_end.  done.
rewrite /= -Heqcall. rewrite /= subst_fset0.
 apply H.  done. move : H1.  simp unfeq.  simpl in *.
case : e;try done. 
destruct e1. 
destruct (eguarded 0 e && econtractive2 e) eqn:Heqn. 
simp unfeq. rewrite /=. rewrite /= {2}Heqn.
pply unfeq_unf in H1.  *)

Lemma is_mue_guarded : forall e i, is_mue e -> eguarded i e.
Proof.
elim;intros;try done.  simpl in *. apply H. done.
Qed. 

Lemma is_mue_cont : forall e, is_mue e -> econtractive2 e.
Proof.
elim;intros;try done. simpl in *. rewrite /= is_mue_guarded //=. auto.
Qed.

Lemma both_is_mue : forall e0 e1, is_mue e0 -> is_mue e1 -> unfeq e0 e1.
Proof.
elim;try done;intros. destruct e1;try done. simp unfeq. case_sum. rewrite /= is_mue_no_subst. apply H.  done. done.
done. rewrite /= is_mue_guarded in e0. rewrite /= is_mue_cont in e0.  done.

done. done.
simp unfeq. case_sum.  rewrite /=  is_mue_no_subst. rewrite /= H.  lia.  done. done. done.
rewrite /= is_mue_guarded in e0. rewrite /= is_mue_cont in e0.  done. done. done.
Qed. 

Lemma is_mue_unfeq : forall e0 e1, is_mue e0 -> unfeq e0 e1 -> is_mue e1.
Proof.
elim;try done;intros.
simpl in *. apply H. done. 
move : H1.  simp unfeq.  case_sum.  rewrite /= is_mue_no_subst //=.
move/orP.    case.  move/eqP=><-.  apply both_is_mue.  done. done. done.
Qed.


Lemma list_eq_trans : forall l0 l1 l2 (f : endpoint -> endpoint -> bool) ,  (forall e0 e1, In e0 l0 -> In e1 l1 -> forall e2 : endpoint, f e0 e1 -> f e1 e2 -> f e0 e2) -> list_eq f l0 l1 -> list_eq f l1 l2 -> list_eq f l0 l2.
Proof.                            
elim. case.  case.  done. done. move => a l l2 f.  done.
move => a l IH.  case.  done.
move => a0 l0. case.  done.
move => a1 l1 f IH2.  simpl in *. split_and.  apply : IH2.  eauto.  eauto.  done. done. apply : IH. all   : eauto.  
Qed. 

Lemma list_eq_trans2 : forall l0 l1 l2 (f : endpoint -> endpoint -> bool) ,  (forall e0 e2, In e0 l0 -> In e2 l2 -> forall e1 : endpoint, f e0 e1 -> f e1 e2 -> f e0 e2) -> list_eq f l0 l1 -> list_eq f l1 l2 -> list_eq f l0 l2.
Proof.                            
elim. case.  case.  done. done. move => a l l2 f.  done.
move => a l IH.  case.  done.
move => a0 l0. case.  done.
move => a1 l1 f IH2.  simpl in *. split_and.  apply : IH2.  eauto.  eauto.  eauto. done. apply : IH. all   : eauto.  
Qed. 


(*Lemma unfeq_rec_left : forall e e', econtractive2 (ERec e) -> unfeq (ERec e) e' = (if e' is ERec e'' then unfeq e e'' else false) || unfeq (e [e (ERec e)..]) e'. 
Proof.
intros. destruct e';simpl in *;try done;simp unfeq;case_sum.
rewrite /= H in e0. done.
rewrite /= H in e0. done.
rewrite /= H in e0. done.
rewrite /= H in e0. done.
rewrite /= H in e0. f_eql done.
Qed.*)



(*Lemma unfeq_in_rec : forall e0 e1 e, unfeq e0 e1 ->  unfeq (ERec e0) e -> unfeq (ERec e1) e.
Proof.
intros. move : H0.  rewrite /= !unfeq_rec_left. 
destruct (isnt_rec e) eqn : Heqn. intros. 
have :  unfeq ([e(ERec e0)..] e0) e. destruct e; try done. 
intros. 


move => v. 
 destru
rewrite /=tftf
 funelim (unfeq e0 e1);try done.
- have : n0 = n1.   move : H. simp unfeq. lia. intros. subst. done. 
-  apply both_is_mue. simpl in *. rewrite /= -unfeq_end.  done.
  move : H0. rewrite /= unfeq_rec_left.    
  destruct (isnt_rec e2) eqn : Heqn. intros.    have : unfeq EEnd e2. 
  destruct e2 ;try done.   rewrite unfeq_end.  done. destruct e2; try done. 
  move/orP.  case.  rewrite /= unfeq_end.  done. simpl in *. rewrite unfeq_end.  done.
  simpl in *. done.
- 
  
simp unfeq.  case_sum. 


simp

move/eqP=><-. done. apply : H. eauto. done. f_equal. rewrite /= -Heqcall.  move : H1.  simp unfeq. case_sum.  inversion H2. subst. eapply H in H0. 
  3 : {  f_equal. 

done.

move => e0 e1 e H. funelim (unfeq e0 e1).
- destruct e;simp unfeq; case_sum;try done.
*)
Lemma unfeq_trans : forall e0 e1 e2, econtractive2 e0 ->   unfeq e0 e1 -> unfeq e1 e2 -> unfeq e0 e2.
Proof.
intros.  funelim (unfeq e0 e2).
- simp unfeq. move : H0 H1. destruct e1; simp unfeq;try done.  lia. 
- simp unfeq. move : H0 H1. destruct e1; simp unfeq;try done.  
- all : try solve [move : H0 H1; destruct e1; simp unfeq ; done].  
- simp unfeq. move : H0 H1. destruct e2; simp unfeq;try done.  
- move : H0.  simp unfeq. intros.  simp unfeq. apply : is_mue_unfeq. eauto. done.
-  simp unfeq. move : H1 H2. destruct e1; simp unfeq;try done.  
  split_and. rewrite /= (eqP H2) (eqP H3) //=.   
  rewrite /= (eqP H9) (eqP H6) //=. rewrite /= (eqP H8) (eqP H5) //=.
  apply : H. simpl in *. done.  eauto.  simpl in *. done.
-  simp unfeq. move : H0 H1. destruct e2; simp unfeq;try done.  
- simp unfeq. move : H1 H2. destruct e1; simp unfeq;try done.  
  split_and. rewrite /= (eqP H1) (eqP H2) //=.   
  rewrite /= (eqP H7) (eqP H5) //=. rewrite /= list_eqP. rewrite /= list_eqP in H6. 
  rewrite /= list_eqP in H4. apply : list_eq_trans2.  2 : { eauto. } 2 : {  eauto. }
  intros. apply : H. eauto. eauto. 
  simpl in *. apply (allP H0). apply/inP. done. eauto. done. 
  f_equal.  done.
- simp unfeq. move : H0 H1. destruct e2; simp unfeq;try done.  
- rewrite /= -Heqcall. move :  H1.  simp unfeq.  case_sum. 
  move/orP. case. move/eqP=> HH.   subst. 
  move : H2. simp unfeq. case_sum. intros. erewrite H. lia. apply econtractive2_subst.  
  split_and.  case.  done. done.
  eauto.  done.
  clear Heq.   rewrite H in e0. done.
Qed.


(*Lemma MUE_imp : forall e, MUE e -> is_mue e.
Proof.
move => e. elim. done. simpl in *. intros. 
rewrite /= is_mue_no_subst in H0.  Print MUE. done. inversion H. done.*)

Lemma is_mue_subst : forall e i sigma, eguarded i e = false -> sigma i = EEnd -> is_mue e [e sigma].
Proof.
elim;rewrite /=;intros.
have : n = i.  lia.  move=>->.  rewrite /= H0.  done.
done. asimpl.  apply : H.  eauto.  simpl in *. rewrite /funcomp.  rewrite /= H1. simpl in *.
done.
done.
done.
Qed. 
Check list_eq. 
(*Lemma unfeq_eq_f : forall a0 a1 (f : endpoint -> endpoint), unfeq a0 a1 -> unfeq (f a0) (f a1).
Proof.
intros.  funelim (unfeq a0 a1).*)
(*Lemma list_eq_map : forall (A B : Type) (l0 l1 : seq A) (f : A -> B) l0 l1 f, list_eq unfeq l0 l1 -> list_eq unfeq (map f l0) (map f l1).*)

Lemma step_test3 : forall g l g' p, step g l g' -> project_pred g /\ size_pred g -> p \notin l.1 ->
 unfeq (project g p) (project g' p).
Proof. 
move => g l g' p H. elim : H p.
- move => a u g0 p Hp Hn. simpl in *.
  rewrite !inE in Hn. ssa. rewrite (negbTE H) (negbTE H0). rewrite unfeq_refl. done. apply cont_project. 
- move => a n gs Hs p Hp Hnp.   simpl in *.
  rewrite !inE in Hnp.  split_and. rewrite (negbTE H) (negbTE H0) match_n.  apply : project_predP_aux.  ssa. eauto. 
  rewrite /= !inE. ssa. done. 

- move => a u l0 g1 g2 Hstep Hunf Hnp p1 HH Hnp1. simpl.  rifliad.   simp unfeq. rewrite /= !eqxx /=.  apply Hunf. ssa. done. 
  simp unfeq. rewrite /= !eqxx /=.  apply Hunf. ssa. done. apply Hunf. ssa. done. 

- move => a l0 gs gs' Hsize Hf0 Hf1 Hnp p1 HH Hnp1. simpl.  rifliad. simp unfeq. rewrite /= !eqxx /=.  
  rewrite list_eqP.
  have : Forall (fun p : gType * gType => unfeq (project p.1 p1) (project p.2 p1))
          (zip gs gs').
  apply/Forall_forall. intros. move : Hf1. move/Forall_forall=> HH1.  apply HH1. done. ssa. 
  move : H0. Search _ (_ \in zip _ _). destruct x. move/in1. simpl. intros. apply (allP H5). done. 
  move : H0. Search _ (_ \in zip _ _). destruct x. move/in1. simpl. intros. apply (allP H4). done. 
  done. 
  clear Hf0 Hf1 HH H Hnp Hnp1. elim : gs gs' Hsize. destruct gs'. simpl in *. intros. done. 
  done. intros. destruct gs'.  done. simpl in *. split_and. inversion x. subst. 
  simpl in *.   done. inversion x. subst. simpl in *. apply H. inversion Hsize. done. done. 

 simp unfeq. rewrite /= !eqxx /=.  
  rewrite list_eqP.
  have : Forall (fun p : gType * gType => unfeq (project p.1 p1) (project p.2 p1))
          (zip gs gs').
  apply/Forall_forall. intros. move : Hf1. move/Forall_forall=> HH1.  apply HH1. done. ssa. 
  move : H1. destruct x. move/in1. simpl. intros. apply (allP H6). done. 
  move : H1. destruct x. move/in1. simpl. intros. apply (allP H5). done. 
  done. 
  clear Hf0 Hf1 HH H Hnp Hnp1. elim : gs gs' Hsize. destruct gs'. simpl in *. intros. done. 
  done. intros. destruct gs'.  done. simpl in *. split_and. inversion x. subst. 
  simpl in *.   done. inversion x. subst. simpl in *. apply H. inversion Hsize. done. done. 
- rewrite /= ! match_n. move : Hf1. 
  simpl in *. move/forallzipP=> Hzip. simpl in *. apply Hzip. done. ssa. ssa. 
  apply (allP H5).  auto.  apply (allP H4). auto.  auto. 

- move => g0 l0 g'0 Hstep Hp p HH Hnp. 




rewrite project_subst in H2. move : H2.  asimpl. simpl in *.  rewrite /= H3.
   have :  ((ERec (project g0 p)) .: var >> project^~ p) = ((ERec (project g0 p)) .: ids).
   fext. case.  simpl in *. done. simpl in *. intros.  done. move =>->. intros.
   apply unfeq_unf.  simpl in *. rewrite H3 /=.  apply cont_project. done.
  intro. destruct x1.  case. simpl. done.  simpl. done. 
   simpl. intros. destruct x2. simpl in H2. done. simpl in H2. inversion H2. subst. done. 
  have : project (GRec g0) p = EEnd. simpl in *. rewrite /= H3.  done.
  intros. have : step (GRec g0) l0 g'0. constructor. done. done. intros.
simpl in H2. rewrite project_subst in H2. move : H2. asimpl. rewrite /= H3. intros. 

have:  [eEEnd .: var >> project^~ p] = [eEEnd .: ids]. fext. case;try done. intros.
rewrite x1 in H2. 
 apply : unfeq_trans.  done. 2 : { eauto. }
 rewrite /= unfeq_end. apply : is_mue_subst. eauto.  done.
 intro. intros.   destruct x1,x2; try (simpl in * ; done). f_equal. inversion H2. done. 
Qed.

(*Operational correspondance, completeness direction*)
Lemma harmony1 : forall g l g' S,  step g l g' -> l.1 `<=` S -> 
 EnvStep (projmap S g) l (projmap S g').
Proof.
intros.
have :  projmap S g =  (projmap S g).[~ptcp_from l.1].[~ptcp_to l.1].[ptcp_from l.1 <- project g (ptcp_from l.1)].[ptcp_to l.1 <- project g (ptcp_to l.1)]. apply/fmapP=>k. rewrite !mapf_if !fnd_set. rifliad. by rewrite (eqP H2). 
by rewrite (eqP H3). Check setf_rem1. Search _ (_.[~_].[? _]). rewrite fnd_rem1 H2. have : ~~false = true by lia. move=>HH. rewrite HH. 
rewrite fnd_rem1 H3 HH. by rewrite mapf_if H1.
exfalso. apply/negP. apply (negbT H1). apply : (fsubset_in). eauto. rewrite !inE H2. lia. exfalso. apply/negP. apply (negbT H1). apply : (fsubset_in). eauto. rewrite !inE H2. lia. rewrite fnd_rem1 H2 fnd_rem1 H3. have : ~~false = true by lia. move => ->. 
rewrite mapf_if H1. done. 
move=>->.

have :  projmap S g' =  (projmap S g').[~ptcp_from l.1].[~ptcp_to l.1].[ptcp_from l.1 <- project g' (ptcp_from l.1)].[ptcp_to l.1 <- project g' (ptcp_to l.1)]. apply/fmapP=>k. rewrite !mapf_if !fnd_set. rifliad. by rewrite (eqP H2). 
by rewrite (eqP H3). Check setf_rem1. Search _ (_.[~_].[? _]). rewrite fnd_rem1 H2. have : ~~false = true by lia. move=>HH. rewrite HH. 
rewrite fnd_rem1 H3 HH. by rewrite mapf_if H1.
exfalso. apply/negP. apply (negbT H1). apply : (fsubset_in). eauto. rewrite !inE H2. lia. exfalso. apply/negP. apply (negbT H1). apply : (fsubset_in). eauto. rewrite !inE H2. lia. rewrite fnd_rem1 H2 fnd_rem1 H3. have : ~~false = true by lia. move => ->. 
rewrite mapf_if H1. done. 
move=>->.
constructor. 
apply step_test. done. apply step_test2. done.
(*apply step_test2. done. *)
by rewrite /projmap /=.
move => p e e'. rewrite !fnd_rem1.  destruct (p != ptcp_to l.1) eqn:Heqn.    destruct (p != ptcp_from l.1) eqn : Heqn2.  intros. 
move : H1. move/[dup]. intro. 
move : H2. rewrite /projmap !mapf_if. rifliad. move=>[] HH [] HH0. rewrite /= -HH -HH0.  apply : step_test3. eauto. rewrite !inE . rewrite /= Heqn Heqn2. done. 
case. move=>->.  move : H3. rewrite mapf_if H1. done. done. done.
Qed.

Check subst_fset0. 

Lemma ren_fset0
     : forall (e : endpoint) sigma,
       (forall n : nat_choiceType, n \in endpoint_fv e -> sigma n = n) ->  e ⟨e sigma ⟩ = e.
Proof.
elim;intros;asimpl.   
rewrite /= H. done. rewrite /= inE. done.
done.
f_equal.  asimpl. apply H. case. done. intros. simpl in *. rewrite /funcomp. rewrite /= H0. done. 
apply/imfsetP.  simpl in *. exists n.+1.  rewrite inE H1. done. done.
f_equal.  apply H.  done.
f_equal. induction l.  done.  simpl in *. f_equal. apply H. done. 
intros.  apply H0.  rewrite /= big_cons inE H1.  done.
apply IHl.  intros.  apply H.  rewrite /= inE H1. lia. done. 
intros.  apply H0.  rewrite /= big_cons inE H1. lia. 
Qed.



(*Lemma subst_step0 : forall e e2 d c vn, econtractive2 (ERec e) -> Estep (ERec e) (d,c,vn) e2 -> exists e', e2 = e' [e (ERec e).. ].
Proof.
intros.  inversion H0.  subst. 
elim;intros. 
-  simpl in *. inversion H0. subst. destruct n.  done. simpl in *. inversion H3. 
- inversion H0.  simpl in *.  subst.  inversion H3. 
- simpl in *. split_and.  have : exists e', e2 = e' [e (ERec e)..]. apply : H. split_and. *)

(*Lemma in2 :
  forall (g : endpoint) [i : nat] [sigma : fin -> endpoint], i \in endpoint_fv ([esigma] g) ->
  (exists n : fin, i \in endpoint_fv (sigma n)).
Proof.
elim;simpl in *;intros. 
exists n. done.
rewrite /= inE in H.  done.
move :H0.  move/imfsetP.  simpl in *. case.  move => x. rewrite /= inE. asimpl.  split_and. subst. 
apply H in H0. destruct H0.  exists x0. destruct x0. simpl in *. rewrite /= inE in H0.  lia. simpl in *. done.
mointros. destruct (i \in endpoint_fv (sigma n)) eqn :Heqn.  done.
exfalso. apply/negP. apply/inotine2. 2 : {  intros.  instantiate (2 := i).  instantiate (1 :=)  erewrite Heqn. 
elim;intros;simpl in *. 
*)
Print endpoint_fv.
(*
Ltac split_eq := apply Bool.eq_true_iff_eq;split.
Notation im := imfsetP.
Lemma map_fv0 : forall e sigma, endpoint_fv (e ⟨e sigma⟩) = [fset sigma n | n in endpoint_fv e].  
Proof.
elim;intros;rewrite /=.
apply/fsetP=> k. rewrite /= inE. split_eq. move/eqP. move=>->. 
apply/imfsetP. simpl in *. exists n.  rewrite /= inE.  done. done.
move/imfsetP=>[] x.  rewrite /= inE. move/eqP=>->.  lia. 
apply/fsetP=>k. split_eq.  rewrite /= inE.  done.
move/imfsetP=>[]x. simpl in *.  rewrite inE.  done. asimpl. 
rewrite /= H. asimpl. 
apply/fsetP=>k.  split_eq. move/imfsetP=>[] x. rewrite /= inE. split_and. 
move: H0.  move/im=>[] x'. simpl in *. intros.  subst.  destruct x'.  done. simpl in *. 

apply/im. simpl in *. exists x'. apply/im.  simpl in *. exists x'.+1. rewrite /= inE.  split_and.  done.
done. move/im=> [] x.  rewrite /=.  move/im=> [] x'.  rewrite /= inE. split_and.  subst. 
apply/im.  simpl in *. exists (sigma x'). rewrite /= inE. split_and. 
apply Bool.ef

 destruct (eqVneq k (sigma n)). apply/imfsetP. 
Lemma map_fv : forall e sigma, endpoint_fv (e [e sigma]) = \bigcup_(i <- endpoint_fv e ) (endpoint_fv (sigma i)).  
Proof.
elim;intros;rewrite /=.  apply/fsetP=>k.  rewrite /= big_exists.  apply Bool.eq_true_iff_eq.  
split.  intros. apply/hasP.  exists n.  rewrite /= inE.  done. done.
move/hasP=>[]. intros. rewrite /= inE in p. rewrite -(eqP p) q. done.
rewrite big_nil.  done. asimpl.  rewrite /= H. 
apply/fsetP=>k. apply Bool.eq_true_iff_eq.  split.  move/imfsetP=>[] x /=. rewrite /= inE.  split_and. 
move : H0. rewrite /= big_exists. move/hasP=>[]. intros. 
rewrite big_exists.    apply/hasP. destruct x eqn:Heqn. done. subst. simpl in *.
exists x0.-1. 2 : { destruct x0.  simpl in *.  rewrite /= inE in q0.  lia. simpl in *.
 move : q0.  asimpl. intros. Search _ (_ \in endpoint_fv (_ ⟨e _ ⟩)).

apply/imfsetP. rewrite /=. exists x0.+2. rewrite /= inE.  split_and. 
rewrite inE. zn

rewrite /= big_cons. 



[fset sigma n | n in endpoint_fv e].*)

Print endpoint. 
Fixpoint not_empt e :=
match e with
| ERec e' => not_empt e'
| EMsg _ _ _ _ => true 
| EBranch _ _ _ => true
| _ => false 
end. 





Lemma subst_step1 : forall e e2 sigma d c vn, econtractive2 e -> (forall v, eguarded v e) ->  Estep (e [e sigma]) (d,c,vn) e2 -> exists e', e2 = e' [e sigma ].
Proof.
move => e e2 sigma d c vn H0 H1 HH. remember (e [e sigma]). elim : HH e Heqe0 H0 H1;intros.  
destruct e;simpl in *. specialize H1 with n. lia. done. 
exists e.  inversion Heqe0.  done. 
all : try done. 
destruct e;simpl in *. specialize H4 with n. lia. done. 
inversion Heqe0.  subst. edestruct H1. eauto. done. apply H3 in H1.  simpl in *. apply H1 in H8. 
exists e.  inversion Heqe0.  done. 
all : try done. 
elim;intros.
- simpl in *. apply : H. eauto. 
- simpl in *. inversion H0. 
- simpl in *. move : H1. asimpl. intros. inversion H1. subst.
  move : H4. asimpl. have : sigma >> ssrfun.id = sigma. fext. intros. done. move =>->. 
  move/H=> HH.  edestruct HH. intros. 
  destruct v.  simpl in *. have : e1 = e2.  admit. 
  intros.  subst. apply : H. intros. 
destruct l. destruct p.  

apply H in H2.  
  inversion H2.  subst. move : H6.  asimpl. 
  rewrite /= H3. 
  exists (x [eERec ([eEVar 0 .: EVar >> ⟨e ↑ ⟩] e) .: ids]). 

  asimpl.
  f_equal.   

Lemma subst_step1 : forall e e2 sigma d c vn, (forall v e1, Estep (sigma v) (d,c,vn) e1 -> exists e', e1 = e' [e sigma] ) ->  Estep (e [e sigma]) (d,c,vn) e2 -> exists e', e2 = e' [e sigma ].
Proof.
elim;intros.
- simpl in *. apply : H. eauto. 
- simpl in *. inversion H0. 
- simpl in *. move : H1. asimpl. intros. inversion H1. subst.
  move : H4. asimpl. have : sigma >> ssrfun.id = sigma. fext. intros. done. move =>->. 
  move/H=> HH.  edestruct HH. intros. 
  destruct v.  simpl in *. have : e1 = e2.  admit. 
  intros.  subst. apply : H. intros. 
destruct l. destruct p.  

apply H in H2.  
  inversion H2.  subst. move : H6.  asimpl. 
  rewrite /= H3. 
  exists (x [eERec ([eEVar 0 .: EVar >> ⟨e ↑ ⟩] e) .: ids]). 

  asimpl.
  f_equal.   
- simpl in *.  inversion H2; subst. exists e.  done. 
  destruct (not_empt e) eqn : Heqn.  edestruct H. done. eauto. eauto. subst. 
  exists (EMsg Sd c v x).  done. destruct e;simpl in *. 
apply H in Heqn. apply 
simpl in *. iapply : H.  done. 
f_equal. f_equal. apply inj_rem4'. intros. 
  case : v H4. simpl in *. done. intros.  simpl in *.
  rewrite /funcomp. have : endpoint_fv (sigma n) = fset0.    apply H1. 
  apply/imfsetP.  simpl in *. exists n.+1.  rewrite /= !inE H8.  done. done.
  intros. rewrite subst_fset0. rewrite ren_fset0. done.
  intros.    rewrite /= x0 in H9. rewrite /= inE in H9. done.
  intros. rewrite /= x0 inE in H9.  done.

 done.  specialize H1 with n.+1. 
  
move : H1. move/imfsetP.   rewrite /= inE.  Check imfsetP.  rewrite /=.
  apply inj_rem4'. intros. case: v H8.  simpl in *. intros. 
  f_equal. apply_i
a
  intros. 
f_equal.  f_equal. f_equal. f_equal.  f_equal. f_equal. Unset Printing Notations. 
done. intros. 
 

Lemma subst_step1 : forall e e2 sigma d c vn, econtractive2 e -> (forall v, v \in endpoint_fv e -> endpoint_fv (sigma v) = fset0) -> 
(endpoint_fv (e [e sigma]) = fset0) ->
(forall v, eguarded v e) -> Estep (e [e sigma]) (d,c,vn) e2 -> exists e', e2 = e' [e sigma ].
Proof.
elim;intros.
- simpl in *. specialize H2 with n.   rewrite /= eqxx in H2. done.
- simpl in *. inversion H3.
- simpl in *. split_and. move : H4. asimpl. intros. inversion H4. subst.
  move : H8. asimpl. have : sigma >> ssrfun.id = sigma. fext. intros. done. move =>->. 
  move/H=> HH.  edestruct HH. 
  done. intros. 
  destruct v.
  simpl in *. rewrite /= -H2. 
  apply/fsetP=> k. apply Bool.eq_true_iff_eq.  split. 
  move/imfsetP=>[] x.  rewrite /= !inE. split_and. simpl in *. subst. apply/imfsetP. simpl in *.
  exists x. rewrite /= inE H9. split_and. done.
  move/imfsetP=>[] x.  rewrite /= !inE. split_and. simpl in *. subst. apply/imfsetP. simpl in *.
  exists x. rewrite /= inE H9. split_and. done.

  simpl in *. rewrite /= H1.  done. apply/imfsetP.  simpl in *. exists v.+1.  rewrite /= inE H0. done. done. 
  move : H2. asimpl. intros. 
  
rewrite /= -H2. 
  apply/fsetP=>k. apply Bool.eq_true_iff_eq.  split. intros. asimpl. 
  apply/imfsetP.  simpl in *. exists k.+1.  rewrite /= inE. split_and. 
  2 : {  done. } 2 : { move/imfsetP. simpl in *. case.  move => x. rewrite /= inE. split_and. subst. 
  move : H0.  asimpl.  intros. destruct x.  done. simpl in *. 

rewrite /= H0.case.  move => x.  rewrite /= !inE. split_and. subst. 
  Search _ (endpoint_fv (_ [e _])). destruct x. done. exfalso.  
  
apply/negP. apply/inotine2. 3 : {  apply : H7.  }  intros. destruct n.  simpl in *. rewrite /= inE.  done.
  simpl in *. rewrite /funcomp.  rewrite ren_fset0. rewrite /= H1. rewrite  inE. done.
  apply/imfsetP. simpl in *. exists n.+1.  rewrite /= inE. split_and. 

Search _ (endpoint_fv _).
 subst. 
case. 

 rewrite inE. intros. 
admit. apply : H2. 
  destruct H0. rewrite /= H0. 
  exists (x [eERec ([eEVar 0 .: sigma >> ⟨e ↑ ⟩] e) .: ids]). 

  split.  asimpl.
  f_equal.   f_equal. f_equal. apply inj_rem4'. intros. 
  case : v H8. simpl in *. done. intros.  simpl in *.
  rewrite /funcomp. have : endpoint_fv (sigma n) = fset0.    apply H1. 
  apply/imfsetP.  simpl in *. exists n.+1.  rewrite /= !inE H8.  done. done.
  intros. rewrite subst_fset0. rewrite ren_fset0. done.
  intros.    rewrite /= x0 in H9. rewrite /= inE in H9. done.
  intros. rewrite /= x0 inE in H9.  done.

 done.  specialize H1 with n.+1. 
  
move : H1. move/imfsetP.   rewrite /= inE.  Check imfsetP.  rewrite /=.
  apply inj_rem4'. intros. case: v H8.  simpl in *. intros. 
  f_equal. apply_i
a
  intros. 
f_equal.  f_equal. f_equal. f_equal.  f_equal. f_equal. Unset Printing Notations. 
done. intros. 
  have : exists e', e2 = e' [ERec ([eEVar 0 .: sigma >> ⟨e ↑ ⟩] e) .: sigma   
  apply : H.  done. 
  case.  done. intros.  apply H1.  apply/imfsetP. simpl in *. 
  exists n.+1. rewrite /= inE. split_and.  done. eauto. 
  move => []. intros. rewrite /= p. exists (x0 [e ERec ( (*sigma >> *) e [e ids]) .: ids]). 
  asimpl. f_equal.  
- apply : H.  simpl in *.  done. simpl in *. done.

f_equal.  f_equal. f_equal. f_equal. 
fmove/H. move => HH. apply : HH.  done. 
  inversion H2. subst. 
eapply HH in H4. 
  edestruct H4.  destruct H0. exists x. split.  eauto. constructor. admit.  
  intros. 
apply H. move/H.


Print Estep. 
Lemma subst_step : forall e e2 sigma d c vn, econtractive2 e -> (forall v, v \in endpoint_fv e -> eguarded v e) -> Estep (e [e sigma]) (d,c,vn) e2 -> exists e', e2 = e' [e sigma ] /\ Estep e (d,c,vn) e'.
Proof.
elim;intros.
- simpl in *. specialize H0 with n.  rewrite /= !inE in H0. exfalso. apply/negP. apply H0. done. done. 
- simpl in *. inversion H1.
- simpl in *. split_and. move : H2. asimpl. intros. 
  have : forall v, v \in endpoint_fv e -> eguarded v e.
  case.  done. intros.  apply H1.  apply/imfsetP. simpl in *. 
  exists n.+1. rewrite /= inE. split_and.  done. move/H. move => HH. eapply HH in H4. 
  edestruct H4.  destruct H0. exists x. split.  eauto. constructor. admit.  
  intros. 
apply H. move/H.


term+)

Print label. Check ch.
Locate "+". Print Estep.

Definition fLabel := ( dir * ptcp * ch * (value + nat))%type.

(*Parameter (f : fLabel). Check (f.1).*)
Definition fType := (gType * option (ptcp * ch * (value + nat)))%type.
Print step. 
Inductive HalfStep : fType -> fLabel -> fType -> Prop  :=
| HS1 a u g p c vn : ptcp_from a = p -> action_ch a = c -> inl u = vn -> 
   HalfStep (GMsg a u g, None) (Sd,p,c,vn) (GMsg a u g, Some (p,c,vn))
| HS2 a u g p0 p1 c vn : ptcp_from a = p0 -> ptcp_to a = p1 -> action_ch a = c -> inl u = vn -> 
   HalfStep (GMsg a u g, Some (p0,c,vn)) (Rd,p1,c,vn) (g, None)
| HS_async a u d g g' f f' p c vn: ptcp_to a <> p -> HalfStep (g,f) (d,p,c,vn) (g',f') ->  
   HalfStep (GMsg a u g,f) (d,p,c,vn) (GMsg a u g', f')
| HS3 a p c vn n gs : ptcp_from a = p -> action_ch a = c -> inr n = vn -> n < size gs -> 
   HalfStep (GBranch a gs, None) (Sd,p,c,vn) (GBranch a gs, Some (p,c,vn))
| HS4 a p0 p1 c vn n gs : ptcp_from a = p0 ->  ptcp_to a = p1 -> action_ch a = c -> inr n = vn ->
   HalfStep (GBranch a gs, Some (p0,c,vn)) (Rd,p1,c,vn) (nth GEnd gs n, None)
| HS5 a p f f' d c vn gs gs' : ptcp_to a <> p ->
   size gs = size gs' -> Forall (fun pp => HalfStep (pp.1,f) (d,p,c,vn)  (pp.2,f')) (zip gs gs') ->
   HalfStep (GBranch a gs, f) (d,p,c,vn) (GBranch a gs', f').
Print label. 

(*Lemma HalfP : forall gp l gp'' f  g g'' p0 c vn p1 d,
 HalfStep gp l gp'' -> gp = (g,None) -> l = (d,p0,c,vn) -> gp'' = (g'',f) ->  exists g', 
 HalfStep (g'',f) (Rd,p1,c,vn) (g',None) /\ step g (Action p0 p1 c,vn) g'.
Proof. 
move => gp l gp'' f g g'' p0 c vn p1 d. elim;intros. 
- inversion H2. inversion H3. inversion H4.  subst. 
*)

Ltac pinv := repeat (match goal with 
                   | [ H : (_,_) = (_,_) |- _ ] => inversion H;clear H
                  end);subst.

Print Estep. Print step. 

Lemma TestProj : forall g p0 c vn e, Estep (project g p0) (Sd,c,vn) e ->
  exists g' p1, project g' p0 = e /\ step g (Action p0 p1 c,vn) g'.
Proof.
move => g p0 c vn e HH.
remember (project g p0).  
remember (Sd,c,vn).
move : HH g c vn p0 Heqe0 Heqp.
elim;intros. 
pinv.  destruct g; simpl in *;try done. move : Heqe0.     case_if.  done. done.
move : Heqe0.  case_if;try done. case.  intros. subst. 
exists g ,(ptcp_to a).  split.  done. rewrite /= (eqP H0). 
have : Action (ptcp_from a) (ptcp_to a) (action_ch a) = a. destruct a.  done. 
move =>->. constructor. admit. 
case_if.  done. intros. exists g ,p0.  rewrite -Heqe0.

apply
Lemma TestProj : forall g p0 p1 c vn e e', Estep (project g p0) (Sd,c,vn) e -> Estep (project g p1) (Rd,c,vn) e' -> 
  exists g', project g' p0 = e /\ project g' p1 = e' /\  step g (Action p0 p1 c,vn) g'.
Proof.
move => g p0 p1 c vn e e' HH. 

remember (project g p1).  
remember (Sd,c,vn).
remember (Rd,c,vn).
move : HH e1 g p0 p1 c vn p2 e' Heqe0 Heqe1 Heqp Heqp2. 
elim. 
- intros.  pinv.
 remember (project g p1).    


as ident
Lemma HalfP : forall gp l0 gp'' l1 gp'  g g'' p0 c vn g' p1,
 HalfStep gp l0 gp'' ->  HalfStep gp'' l1 gp' -> gpred g ->
gp = (g,None) -> gp'' = (g'',Some (p0,c,vn)) -> gp' = (g',None) ->
l0 = (Sd,p0,c,vn) -> l1 = (Rd,p1,c,vn) ->  step g (Action p0 p1 c,vn) g'. 
Proof. 
move => gp l0 gp'' l1 gp' g g'' p0 c vn g' p1.  
elim. 
- intros. pinv. clear H15 H14 H13. 
  inversion H2.  subst. e

   move =>->. constructor. done.
   subst. apply GR3. done.

move => a u g0 p c0 vn0 H0 H1 H2 HH.
  remember ((GMsg a u g0, Some (p, c0, vn0))).
  move : HH a u g0 p c0 vn0 H0 H1 H2 Heqp2.
  elim;intros. 
 * pinv.
 * pinv.
   have : Action (ptcp_from a0) (ptcp_to a0) (action_ch a0) = a0. destruct a0.   done.
   move =>->. constructor. done.
 * pinv. apply : H1.  4 : {  f_equal.  apply GR3. done. 
  inversion Heqp.  
  inversion Heqp.  subst.  inversion H7. subst.  inversion H5. subst. 
  inversion Heqp2.  subst. 
  apply IHHalfStep.
induction H2.  inversion H7. subst. inversion H4. subst. inversion H5. subst. 
  inversion H2. 

   move =>->.  constructor. done.
 * subst. inversion 
done.

inversion Heqp. subst. clear Heqp. inversion H2. subst. 
  * Print step. 
constructor. 




induction H. 
Admitted. 

Parameter (p : fLabel). Check (p.1).



Definition projHalf g p (f : fLabel) e := Estep (project g p) (Sd,f.1.2,f.2) e.


Lemma harmony2_1 : forall e0 c vn e1 p, Estep e0 (Sd,c,vn) e1 -> exists g g', project g p = e0 /\ projHalf g p (p,c,vn) e1 /\
                                                                     HalfStep1 g (g',(p,c,vn)). 
Proof. Admitted.

Lemma harmony2_2 : forall e0 c vn e1 p, Estep e0 (Rd,c,vn) e1 -> exists g g', project g p = e0 /\ project g' p = e1 /\
                                                                     HalfStep2 (g,(p,c,vn)) (g',(p,c,vn)). 
Proof. Admitted.w


Lemma harmony2 : forall g l d  S,
 EnvStep (projmap S g) l d ->  exists g', projmap S g' = d /\ step g l g'.  
Proof.
intros. destruct H.  inversion H. subst. 
