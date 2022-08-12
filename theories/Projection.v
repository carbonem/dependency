From mathcomp Require Import all_ssreflect zify.
From mathcomp Require Import finmap.


From Dep Require Export NewSyntax Substitutions.

(*Let inE := NewSyntax.inE.*)

From Equations Require Import Equations.

Lemma esize0 : forall e, 1 <= esize e.
Proof.
elim;intros;try done. 
simpl in *. destruct l. done. simpl in *.
have : 0 < esize e. apply H.  done. intros.  
lia.  
Qed.
Check esize0. 
Lemma foldr0 : forall l, 0 < (foldr (fun e0 : endpoint => addn (esize e0)) 1 l).
Proof.
intros. destruct l.  done. simpl in *. move : (esize0 e). intros. lia. 
Qed. 


Hint Resolve esize0 foldr0.


Equations foldIn {A B : Type} (l : list A) (f : forall (x : A), B -> List.In x l -> B) (b : B) : B := 
foldIn nil f b := b;
foldIn (x:: xs) f b := f x (foldIn xs (fun x b H => f x b _) b) _. 

Print Equations.Prop.Subterm.lexprod.

Definition mltn n0 n1 := n0 < n1 = true.

Lemma in1 : forall (A B: eqType) (a : A) (b : B) al bl, (a, b) \in zip al bl -> a \in al. 
Proof.
move => A B a b. elim.  case. done. done. simpl in *. intros. destruct bl. simpl in *. done.
simpl in *. move : H0. rewrite /= !inE. move/orP. case.  move/eqP. case.  intros. subst.  rewrite /= eqxx. done.
intros. erewrite  H. lia.  eauto.
Qed. 

Lemma in2 : forall (A B: eqType) (a : A) (b : B) al bl, (a, b) \in zip al bl -> b \in bl. 
Proof.
move => A B a b. elim.  case. done. done. simpl in *. intros. destruct bl. simpl in *. done.
simpl in *. move : H0. rewrite /= !inE. move/orP. case.  move/eqP. case.  intros. subst.  rewrite /= eqxx. done.
intros. erewrite  H. lia.  eauto.
Qed. 

Lemma in_fold : forall es e, e \in es -> esize e < foldr (fun e1 : endpoint => addn (esize e1)) 1 es.
Proof.
elim. done. simpl in *. intros. rewrite /= inE in H0. destruct (orP H0). rewrite /= (eqP H1).
move : (foldr0 l). lia. apply H in H1.  lia. 
Qed.



Lemma emu_height_ren : forall g sigma, emu_height g ⟨e sigma ⟩  = emu_height g.
Proof.
elim;rewrite /=;try done;intros.
f_equal. apply : H. 
Qed.



Lemma emu_height_subst : forall g0 sigma i,  eguarded  i g0 -> (forall n, n != i -> emu_height (sigma n) = 0) -> econtractive2 g0 -> emu_height (g0[e sigma]) = emu_height g0.
Proof. 
elim; try solve [by rewrite /=];intros.
- asimpl. simpl in H. rewrite H0. done. apply : H. 
simpl. f_equal. asimpl. apply H with (i:=i.+1). 2 : { intros. destruct n. simpl. done. simpl. asimpl.
rewrite emu_height_ren. apply H1. lia.  } intros. apply : H0. eauto. simpl in H2. split_and.
Qed. 



Definition emu_height_subst0 g0 sigma :=  (@emu_height_subst g0 sigma 0).
Require Import Program.


Show Obligation Tactic.

Obligation Tactic := program_simpl; try solve [ constructor;lia | simpl in *;constructor; apply/ltP; apply in_fold;apply : in2;apply/inP |
constructor 2;split_and;rewrite /= emu_height_subst0; (try lia); (try done);case; simpl in *; done
]; try done.



Fixpoint is_mue e :=
match e with
| ERec e' => is_mue e'
| EEnd => true
| _ => false 
end.
Check list_eq.

Equations list_eq2 (es0 es1 : seq endpoint)  (f : forall e0 e1, In e0 es0 -> In e1 es1 -> bool )  : bool :=
 list_eq2 nil nil f => true;
 list_eq2 (e::es') (e1::es1') f => (@f e e1 _ _) && list_eq2 es' es1' (fun e0 e1 H0 H1 => f e0 e1 _ _);
 list_eq2 _ _ _ => false. 


Lemma list_eqP : forall l0 l1 f, list_eq2 l0 l1 (fun e0 e1 (_ : In e0 l0) (_: In e1 l1) => f e0 e1) = list_eq f l0 l1.  
Proof.
elim. case.  done. done.
move => a l IH.  case.  done. simpl in *. intros. simp list_eq2.  f_equal. done.
Qed. 


Definition is_rec e := if e is ERec _ then true else false.

(*The change that made transitivity possible was in ERec, either syntactic eq or unfold, we dont need recuprev call unfeq e0 e1 on unfeq ERec e0 ERec e1 because that allows unfoldings under ERec which we dont need*)
Equations unfeq (e0 e1 : endpoint) : bool by wf (esize e1,emu_height e0) 
              ((Equations.Prop.Subterm.lexprod _ _ lt lt)) := {
unfeq (EVar n0) (EVar n1) =>  n0 == n1; 
unfeq EEnd e => is_mue e;
unfeq (EMsg d0 c0 v0 e0') (EMsg d1 c1 v1 e1') => (d0 == d1) && (c0 == c1) && (v0 == v1) && ((unfeq e0' e1' )) ;
unfeq (EBranch d0 c0 es0) (EBranch d1 c1 es1) => (d0 == d1) && (c0 == c1) && (list_eq2  es0 es1 (fun e0 e1 H0 H1 => unfeq e0 e1)); (* ((foldIn (zip es0 es1) (fun x b H => b && ((unfeq x.1 x.2) ) ) true));*)
unfeq (ERec e0') e1 with (dec (econtractive2 (ERec e0'))) => {
  unfeq (ERec e0') e1 (left _)  => ((ERec e0') == e1) || ((unfeq (e0' [e (ERec e0').:ids]) e1));(*Shifting is wrong but lets keep it as it is for now and later see where it blows up*)
  unfeq _ _ (right _) => false
 };

(*  => {
unfeq (ERec e0') e1 with (dec (econtractive2 (ERec e0'))) => {
  unfeq (ERec e0') (ERec e1') (left _) => (unfeq e0' e1') || (unfeq (e0' [e (ERec e0').:ids]) (ERec e1'));
  unfeq (ERec e0') e1 (left _) =>  unfeq (e0' [e (ERec e0').:ids]) e1;
  unfeq _ _ (right _) => false };*)

unfeq _ _ => false}.  
Next Obligation.
simpl in *;constructor; apply/ltP.  apply in_fold. apply/inP. done. Qed. 
Next Obligation. Qed.





Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.






Fixpoint project g p := 
match g with 
| GEnd => EEnd
| GMsg a u g0 => if p == (ptcp_from a) then EMsg Sd (action_ch a) u (project g0 p) 
                               else if p == (ptcp_to a) then EMsg Rd (action_ch a) u (project g0 p) else project g0 p
| GBranch a gs => if p == (ptcp_from a) then EBranch Sd (action_ch a) (map (fun g => project g p) gs)
                                else if p == (ptcp_to a) then EBranch Rd (action_ch a) (map (fun g => project g p) gs) else if gs is g'::gs' then project g' p else EEnd
| GRec g => if eguarded 0 (project g p) then ERec (project g p) else EEnd
| GVar n => EVar n
end.

Lemma match_n : forall (gs : seq gType) k,  match gs with
  | [::] => EEnd
  | g'0 :: _ => project g'0 k end = project (nth GEnd gs 0) k.
Proof.
elim. done. intros. rewrite /=. done.
Qed.

Lemma big_exists : forall (A : eqType) (B : choiceType) (l : seq A) (f0 : A -> {fset B}) p, p \in \bigcup_(j <- l) (f0 j) = has (fun x => p \in f0 x) l. 
Proof. 
move => A B. elim. move => f0 p. rewrite big_nil. done. intros. simpl. rewrite big_cons !inE. destruct ( (p \in f0 a) ) eqn:Heqn;rewrite /=. 
 done.
apply H.
Qed.

Lemma eguarded_ren : forall g sigma i , (forall n, sigma n != i) -> eguarded i g -> eguarded i g ⟨e sigma⟩.
Proof.
elim;rewrite /=;simpl;intros;try done.
asimpl. apply : H. intros. destruct n.  done. simpl. specialize H0 with n. rewrite /funcomp. lia.
done. 
Qed.

Lemma eguarded_shift1 : forall g i sigma, injective sigma ->  eguarded i g -> eguarded (sigma i) g ⟨e sigma⟩.
Proof.
elim;rewrite /=;simpl;intros;try done.
apply/eqP. move=> HH. apply H in HH. lia. 
asimpl. 
have : (sigma i).+1 = ((0 .: sigma >> succn) i.+1).
destruct i.  simpl. rewrite /funcomp. done. simpl. rewrite /funcomp. done.
move=>->. apply H. intro. intros. destruct x1;destruct x2;try done. inversion H2. f_equal.  apply/H0. done. 
done. 
Qed.


(*Lemma injective_lift_ren : forall sigma, injective sigma -> injective (0 .: sigma >> succn). 
Proof. 
intros. intro. case. simpl. destruct x1.  done.  simpl.  done.
intro.  simpl. destruct x1. done. simpl. intros. f_equal. apply H. inversion H0. done. 
Qed. 

Lemma injective_shift : injective S.
Proof. intro. intros. inversion H.  done. Qed.

Hint Resolve injective_shift  injective_lift_ren.*)


Lemma eguarded_shift2 : forall g i sigma, injective sigma ->  eguarded (sigma i) g ⟨e sigma⟩ ->  eguarded i g.
Proof.
elim;rewrite /=;simpl;intros;try done.
apply/eqP. move=> HH. apply (negP H0). apply/eqP. f_equal. done. 
apply :H.  2 : { apply : H1.  } 
asimpl. auto. 
Qed.


Lemma eguarded_shift : forall g sigma i , injective sigma  -> eguarded i g <-> eguarded (sigma i) g ⟨e sigma⟩.

intros. split;intros; eauto using eguarded_shift1, eguarded_shift2.
Qed.


Lemma eguarded_fv2 : forall g v, eguarded v g = false -> endpoint_fv g = [fset v]. 
Proof.
elim;rewrite /=;try done;intros. have : n = v.  lia.  move=>->.  done.
erewrite H. 2 : { eauto.  } apply/fsetP.  move => k. rewrite /= !inE. 

Search _ ( (_ <-> _) -> (_ = _)). apply Bool.eq_true_iff_eq. split.  
move/imfsetP=> []. simpl in *. move => x. rewrite /= !inE. split_and. subst. rewrite /= (eqP H1). simpl in *. rewrite /= eqxx. done. 
move/eqP. move=>->.  apply/imfsetP. simpl in *. exists v.+1.  rewrite /= !inE. split_and. done.
Qed. 



Lemma inj_rem4 : forall e  f f' , 
(forall v, v \in endpoint_fv e -> f v = f' v) -> e ⟨e f⟩  = e ⟨e f'⟩ .
Proof.  
elim;intros.
- asimpl. rewrite H.  done. rewrite /= !inE //=. done.
asimpl. f_equal.  apply H.  intros. destruct v. done. asimpl. rewrite H0. done. 
simpl. apply/imfsetP. exists v.+1. simpl. rewrite !inE. split_and. done. asimpl. f_equal. apply H. auto. 
asimpl. f_equal. apply/eq_in_map. move => g. intros. apply H. done. intros.  apply H0.
simpl. rewrite big_map. rewrite big_exists. apply/hasP. exists g. done. done.
Qed.

Lemma inj_rem5 : forall e  f f' v , 
 e ⟨e f⟩  = e ⟨e f'⟩ ->  f v <> f' v -> v \notin endpoint_fv e.
Proof.  
elim;intros;rewrite /= ?inE;try done. move : H. asimpl. case. intros. destruct (eqVneq v n). subst. done. done. 
move : H0. asimpl. case. move/H=>HH. apply/negP. move/imfsetP=>[] x /=. rewrite !inE. split_and. 
specialize HH with v.+1.  move : HH. asimpl. move => HH. have : (f v).+1 <> (f' v).+1. move => H'. inversion H'. apply H1. 
done.  move/HH. subst. simpl. destruct x. done. simpl. simpl in *. rewrite H0 //=. 
apply: H. move : H0. asimpl. case. eauto. eauto.
rewrite big_map big_exists. move : H0. asimpl. case. move/eq_in_map=>HH.
apply/negP.  move/hasP=>[] x. intros. apply/negP. apply  H with (f:=f)(f':=f'). all : eauto. 
Qed.


Lemma inj_rem4' : forall e  f f' , 
(forall v, v \in endpoint_fv e -> f v = f' v) -> e [e f]  = e [e f'] .
Proof.  
elim;intros.
- asimpl. rewrite H.  done. rewrite /= !inE. done.
done. asimpl. f_equal.  apply H.  intros. destruct v. done. asimpl. rewrite H0. done. 
simpl. apply/imfsetP. exists v.+1. simpl. rewrite !inE. split_and. done. asimpl. f_equal. apply H. auto. 
asimpl. f_equal. apply/eq_in_map. move => g. intros. apply H. done. intros.  apply H0.
simpl. rewrite big_map. rewrite big_exists. apply/hasP. exists g. done. done.
Qed.


Lemma injsimpl_rem : forall e0 e1 f f', injective f  -> e0 ⟨e f⟩ = e1 ⟨e f⟩ -> e0 ⟨e f' ⟩ = e1 ⟨e f' ⟩.
Proof. 
elim. intros. destruct e1;try done.  f_equal. move : H0. asimpl. case. move/H. by move=>->. 
- case;try done.
- intros. asimpl.  destruct e1;try done. f_equal. move : H1.  asimpl. intros. f_equal. 
  apply : H. have : injective (0 .: f >> succn ).
  intro. intros. destruct x1;destruct x2. done. move : H.  asimpl.
done.  move : H. asimpl. done. f_equal. move : H. asimpl. case. move/H0. done. move => HH. apply : HH. 

(*intro. intros. destruct x1;destruct x2. done. move : H.  asimpl.
done.  move : H. asimpl. done. f_equal. move : H. asimpl. case. move/H1. done. *)
  move : H1.  asimpl. case. intros. eauto.
- intros. destruct e1;try done.
 move : H1.  asimpl. case. intros.  subst. f_equal. eauto. 
- intros. move : H1.  asimpl. destruct e1;try done. asimpl. case. intros. subst. f_equal.
  move : H3. elim : l l0 H;simpl. destruct l0. done. done. destruct l0. done. 
  simpl. intros. f_equal. apply : H1. auto. eauto. inversion H3. done.  apply H. 
  intros. apply : H1. eauto. eauto. eauto.  inversion H3. eauto. 
Qed.



Lemma inj_rem : forall e0 e1 f f', injective f  -> e0 ⟨e f⟩ = e1 ⟨e f⟩ -> e0 ⟨e f' ⟩ = e1 ⟨e f' ⟩.
Proof. 
elim. intros. destruct e1;try done.  f_equal. move : H0. asimpl. case. move/H. by move=>->. 
- case;try done.
- intros. asimpl.  destruct e1;try done. f_equal. move : H1.  asimpl. intros. f_equal. 
  apply : H. have : injective (0 .: f >> succn ).
  intro. intros. destruct x1;destruct x2. done. move : H.  asimpl.
done.  move : H. asimpl. done. f_equal. move : H. asimpl. case. move/H0. done. move => HH. apply : HH. 

(*intro. intros. destruct x1;destruct x2. done. move : H.  asimpl.
done.  move : H. asimpl. done. f_equal. move : H. asimpl. case. move/H1. done. *)
  move : H1.  asimpl. case. intros. eauto.
- intros. destruct e1;try done.
 move : H1.  asimpl. case. intros.  subst. f_equal. eauto. 
- intros. move : H1.  asimpl. destruct e1;try done. asimpl. case. intros. subst. f_equal.
  move : H3. elim : l l0 H;simpl. destruct l0. done. done. destruct l0. done. 
  simpl. intros. f_equal. apply : H1. auto. eauto. inversion H3. done.  apply H. 
  intros. apply : H1. eauto. eauto. eauto.  inversion H3. eauto. 
Qed.

Lemma inj_rem2 : forall e0 e1 f , injective f  -> e0 ⟨e f⟩ = e1 ⟨e f⟩ -> e0 = e1.
Proof. intros. have : e0 = e0 ⟨id⟩.  asimpl. done. move=>->. 
have : e1 = e1 ⟨id⟩. asimpl. done. move=>->. apply/inj_rem. eauto. eauto.
Qed.



Lemma inj_rem5' : forall e  f f' v , 
 e [e f]  = e [e f'] ->  f v <> f' v -> v \notin endpoint_fv e.
Proof.  
elim;intros;rewrite /= ?inE;try done. move : H. asimpl. case. intros. destruct (eqVneq v n). subst. done. done. 
move : H0. asimpl. case. move/H=>HH. apply/negP. move/imfsetP=>[] x /=. rewrite !inE. split_and. 
specialize HH with v.+1.  move : HH. asimpl. move => HH. have :  (f v) ⟨e ↑ ⟩ <> (f' v) ⟨e ↑ ⟩.  
 move => H'. apply inj_rem2 in H'. apply H1. done. intro. rewrite /shift.  intros. inversion H3. done. 
move/HH. subst. simpl. destruct x. done. simpl. simpl in *. rewrite H0 //=. 
apply: H. move : H0. asimpl. case. eauto. eauto.
rewrite big_map big_exists. move : H0. asimpl. case. move/eq_in_map=>HH.
apply/negP.  move/hasP=>[] x. intros. apply/negP. apply  H with (f:=f)(f':=f'). all : eauto. 
Qed.



Lemma project_ren : forall g p sigma, injective sigma ->  project (g ⟨ sigma ⟩) p = (project g p) ⟨ sigma ⟩.
Proof.
elim;intros.
- simpl. done.
- done.
- simpl. asimpl. rewrite H. symmetry. case_if.
  * asimpl. case_if. done. have : 0 = (0.: sigma >> succn ) 0. done. intros. rewrite {1}x in H2.
    eapply eguarded_shift in H1. erewrite H1 in H2. done. auto. 
    case_if. have : 0 = (0.: sigma >> succn ) 0. done. intros. rewrite {1}x in H2. 
    apply eguarded_shift in H2. rewrite H2 in H1. done. auto. done. simpl in *. auto. 
    auto. 
- simpl in *.
rifliad;asimpl;try done. f_equal. auto.  f_equal. auto. auto.
simpl. rifliad;asimpl;try done. f_equal. rewrite -!map_comp. apply/eq_in_map=>l'. intros. simpl.
apply H. done.  done.
 f_equal. rewrite -!map_comp. apply/eq_in_map=>l'. intros. simpl.
apply H. done. done.
rewrite !match_n. induction l. done. simpl. apply H. auto. done.
Qed.




Lemma eguarded_sig2_ren : forall g sigma sigma' i, eguarded i g ⟨e sigma⟩ -> (forall n, (sigma n) != i ->  (sigma' n) != i) -> eguarded i g ⟨e sigma'⟩.
Proof.
elim;rewrite /=;intros;try done.
apply H0. done.
asimpl. apply : H. eauto. move => n.  asimpl. simpl. intros. destruct n. done. simpl in *. 
move : H. rewrite /funcomp. intros. suff :  sigma' n != i.  lia. apply : H1. lia. 
Qed.

Lemma eguarded_sig2 : forall g sigma sigma' i, eguarded i g [e sigma] -> (forall n, eguarded i (sigma n) -> eguarded i (sigma' n)) -> eguarded i g [e sigma'].
Proof.
elim;rewrite /=;intros;try done.
apply H0. done.
asimpl. apply : H. eauto. move => n.  asimpl. simpl. intros. destruct n. done. simpl in *.
move : H. rewrite /funcomp. specialize H1 with n. move : H0. asimpl.
intros. rewrite -eguarded_shift. move : H. rewrite -eguarded_shift.  move/H1. done. 
done. done. 
Qed.


Lemma eguarded_fv : forall g v, v \notin endpoint_fv g -> eguarded v g.
Proof.
elim;rewrite /=;try done;intros.
rewrite !inE in H. lia.
apply H. move : H0. move/imfsetP=>HH. apply/negP=>HH'. apply HH. simpl. exists v.+1;try done.  
rewrite !inE. split_and.
Qed.

Lemma inotine : forall g i sigma, (forall n, i !=  sigma n) -> i \notin endpoint_fv g ⟨e sigma ⟩.
Proof.
elim;rewrite /=;try done;intros. rewrite !inE. specialize H with n. lia.
apply/imfsetP=>/=H'. destruct H'. rewrite !inE in H1.  destruct (andP H1). move : H3. asimpl. intros. apply/negP. apply : H. 2 : { apply : H3. } case. simpl. done. simpl. intros. asimpl. destruct x.  done. suff : x != sigma n. lia. 
specialize H0 with n.  simpl in H2. subst. done. 
rewrite !big_map big_exists. apply/negP. move/hasP=>HH. destruct HH. apply/negP. apply : H. eauto.
2 : {  apply : H2. } auto.
Qed.
Open Scope fscope. 
Lemma inject_ren : forall (sigma : nat -> nat), injective sigma -> injective (⟨g sigma ⟩).
Proof.
intros. intro. move : x1 sigma H. elim; intros. 
destruct x2; simpl in *. inversion H0. f_equal. apply H. done. all : try done.
destruct x2; simpl in *. inversion H0. done. all : try done.
destruct x2; simpl in *. all : try done. f_equal. inversion H1. apply : H. 2 : {  eauto.  }
asimpl. auto. simpl in *. destruct x2; try done. simpl in *. inversion H1. subst. f_equal.  
apply : H. eauto. done.  
destruct x2; try done. simpl in *. inversion H1. subst. f_equal.  
move : H4. clear H1. move : l l0 H. elim. intros. destruct l0. done. simpl in *.  done.
intros. destruct l0.  simpl in *. done. simpl in *.  inversion H4. f_equal. apply : H1. done. apply H0. done. 
apply H. intros. apply : H1. rewrite /= inE. apply/orP. right. done. apply H6. apply H7. done.
Qed.


Lemma inject_endsimpl : forall sigma, injective sigma -> injective (var 0 .: sigma >> ⟨g ↑ ⟩).
Proof.
intros. intro. intros. destruct x1,x2; try done. simpl in *. 
rewrite /funcomp in H0. destruct (sigma x2); try done. simpl in *. rewrite /funcomp in H0. destruct (sigma x1); try done.
f_equal. simpl in *. 
rewrite /funcomp in H0. apply H. apply : inject_ren. 2 : { eauto. } done.
Qed.


Lemma project_subst : forall g p sigma, injective sigma ->  project (g[g sigma]) p = (project g p) [ sigma >> (fun g => project g p)].
Proof.
elim;intros.
- simpl. done.
- done.
- simpl. asimpl. rewrite H. symmetry. case_if. case_if. simpl in *. f_equal. asimpl. simpl in *. 
  f_equal. rewrite /funcomp. fext. intros. destruct x. done. simpl in *. 
  rewrite /= project_ren.  done. done. 

have :  eguarded 0 (project g p) [e(var 0 .: sigma >> ⟨g ↑ ⟩) >> project^~ p].
apply : eguarded_sig2. instantiate (1 := ids). asimpl.  done. simpl in *. intros.
destruct n. done. asimpl. rewrite project_ren. apply eguarded_fv. apply inotine. done. done. 
intros. rewrite x in H2.  done.  case_if. 
have : eguarded 0 (project g p) [e ids]. eapply eguarded_sig2. eauto. intros. destruct n.  simpl in *. done.
simpl in *. done.
  asimpl. intros. rewrite x in H1. done. simpl in *. done. 
(*f_equal. 

 asimpl. apply inj_rem4'. intros. apply eguarded_fv2 in H1.  rewrite /= H1 in H3. 
    rewrite /= inE in H3.  rewrite /= (eqP H3). simpl in *. done.*)
 apply inject_endsimpl. done.
simpl.
rifliad;asimpl;try done. f_equal. auto.  f_equal. auto. auto.
simpl. rifliad;asimpl;try done. f_equal. rewrite -!map_comp. apply/eq_in_map=>l'. intros. simpl.
apply H. done. done. 
 f_equal. rewrite -!map_comp. apply/eq_in_map=>l'. intros. simpl.
apply H. done.  done.
rewrite !match_n. induction l. done. simpl. apply H. auto. done.
Qed.




Definition fset_ptcp := {fset ptcp}.
Definition env := {fmap ptcp -> endpoint}.
Definition projmap  (S : fset_ptcp) (g : gType)  : env := [fmap p : S => project g (val p)].


Definition ptcp_le (p0 p1 : ptcp) := let: Ptcp n0 := p0 in let: Ptcp n1 := p1 in n0 <= n1.

  Lemma nat_list_max : forall (xs : list ptcp),
    { n : ptcp | forall x, x \in xs -> ptcp_le x  n }.
  Proof.
    induction xs as [ | x xs [y H] ].
    (* case: nil *)
    exists (Ptcp 0). inversion 1.
    (* case: cons x xs *) destruct x,y.
    exists (Ptcp (n + n0)%nat). intros z J. move : J. rewrite inE. move/orP=>[]. move/eqP=>->. rewrite /=. lia. move/H. rewrite /ptcp_le. destruct z.  lia. 
   Qed.

 Lemma atom_fresh_for_list :
    forall (xs : list ptcp), { n : ptcp | ~ n \in xs }.
  Proof.
    intros xs. destruct (nat_list_max xs) as [x H]. destruct x. exists (Ptcp (n.+1)).
    intros J. rewrite /ptcp_le in H. apply H in J. lia. 
  Qed. 



Definition fresh (S : fset_ptcp) :=
    match atom_fresh_for_list S with
      (exist x _ ) => x
    end.




Fixpoint project_pred  (g : gType):=  
match g with 
| GMsg a u g0 => project_pred g0 
| GBranch a gs => let S := ptcps g in 
                 all (fun (g' : gType)  => 
                         all (fun p => unfeq (project (nth GEnd gs 0) p) (project g' p)) 
                         (fresh S |` (S `\` a )))
                      gs 
                 && (all project_pred gs)
| GRec g0 => project_pred g0
| _ => true 
end.
