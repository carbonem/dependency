From mathcomp Require Import all_ssreflect zify.
From mathcomp Require Import finmap.


From Equations Require Import Equations.

From Dep Require Import NewSyntax Bisimulation.


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

Check in_left. Print Sumbool.sumbool_of_bool.
(*Lemma unfeq_elim2
     : forall P : endpoint -> endpoint -> bool -> Type,
       (forall n0 n1 : fin, P (EVar n0) (EVar n1) (n0 == n1)) ->
       (forall n : fin, P (EVar n) EEnd false) ->
       (forall (n : fin) (d : dir) (c : ch) (v : value) (e : endpoint), P (EVar n) (EMsg d c v e) false) ->
       (forall (n : fin) (d0 : dir) (c0 : ch) (l : seq endpoint), P (EVar n) (EBranch d0 c0 l) false) ->
       (forall (n : fin) (e0 : endpoint), P (EVar n) (ERec e0) false) ->
       (forall e : endpoint, P EEnd e (is_mue e)) ->
       (forall (d : dir) (c : ch) (v : value) (e : endpoint) (n : fin), P (EMsg d c v e) (EVar n) false) ->
       (forall (d : dir) (c : ch) (v : value) (e : endpoint), P (EMsg d c v e) EEnd false) ->
       (forall (d0 : dir) (c0 : ch) (v0 : value) (e0' : endpoint) (d1 : dir) (c1 : ch) (v1 : value) (e1' : endpoint),
        P e0' e1' (unfeq e0' e1') -> P (EMsg d0 c0 v0 e0') (EMsg d1 c1 v1 e1') ((d0 == d1) && (c0 == c1) && (v0 == v1) && unfeq e0' e1')) ->
       (forall (d : dir) (c : ch) (v : value) (e : endpoint) (d1 : dir) (c1 : ch) (l : seq endpoint), P (EMsg d c v e) (EBranch d1 c1 l) false) ->
       (forall (d : dir) (c : ch) (v : value) (e e1 : endpoint), P (EMsg d c v e) (ERec e1) false) ->
       (forall (d0 : dir) (c0 : ch) (l : seq endpoint) (n : fin), P (EBranch d0 c0 l) (EVar n) false) ->
       (forall (d0 : dir) (c0 : ch) (l : seq endpoint), P (EBranch d0 c0 l) EEnd false) ->
       (forall (d0 : dir) (c0 : ch) (l : seq endpoint) (d : dir) (c : ch) (v : value) (e : endpoint), P (EBranch d0 c0 l) (EMsg d c v e) false) ->
       (forall (d0 : dir) (c0 : ch) (es0 : seq endpoint) (d1 : dir) (c1 : ch) (es1 : seq endpoint),
        (forall e0 e1 : endpoint, In e0 es0 -> In e1 es1 -> P e0 e1 (unfeq e0 e1)) ->
        P (EBranch d0 c0 es0) (EBranch d1 c1 es1) ((d0 == d1) && (c0 == c1) && list_eq unfeq es0 es1)) ->
       (forall (d0 : dir) (c0 : ch) (l : seq endpoint) (e0 : endpoint), P (EBranch d0 c0 l) (ERec e0) false) ->
       (forall (e0' : endpoint) (e : econtractive2 (ERec e0') = true) (n : fin),
        P e0' [e(ERec e0')..] (EVar n) (unfeq e0' [e(ERec e0')..] (EVar n)) ->   econtractive2 (ERec e0')  -> P (ERec e0') (EVar n) (unfeq e0' [e(ERec e0')..] (EVar n))) ->
       (forall (e0' : endpoint) (e : econtractive2 (ERec e0') = true),
        P e0' [e(ERec e0')..] EEnd (unfeq e0' [e(ERec e0')..] EEnd) ->  econtractive2 (ERec e0') ->  P (ERec e0') EEnd (unfeq e0' [e(ERec e0')..] EEnd)) ->
       (forall (e0' : endpoint) (e : econtractive2 (ERec e0') = true) (d : dir) (c : ch) (v : value) (e0 : endpoint),
        P e0' [e(ERec e0')..] (EMsg d c v e0) (unfeq e0' [e(ERec e0')..] (EMsg d c v e0)) ->  econtractive2 (ERec e0') -> P (ERec e0') (EMsg d c v e0) (unfeq e0' [e(ERec e0')..] (EMsg d c v e0))) ->
       (forall (e0' : endpoint) (e : econtractive2 (ERec e0') = true) (d0 : dir) (c0 : ch) (l : seq endpoint),
        P e0' [e(ERec e0')..] (EBranch d0 c0 l) (unfeq e0' [e(ERec e0')..] (EBranch d0 c0 l)) ->  econtractive2 (ERec e0') -> P (ERec e0') (EBranch d0 c0 l) (unfeq e0' [e(ERec e0')..] (EBranch d0 c0 l))) ->
       (forall (e0' : endpoint) (e : econtractive2 (ERec e0') = true) (e1' : endpoint),
        P e0' e1' (unfeq e0' e1') ->
        P e0' [e(ERec e0')..] (ERec e1') (unfeq e0' [e(ERec e0')..] (ERec e1')) ->  econtractive2 (ERec e0') ->  P (ERec e0') (ERec e1') (unfeq e0' e1' || unfeq e0' [e(ERec e0')..] (ERec e1'))) ->
       (forall (e0' : endpoint) (e0 : econtractive2 (ERec e0') = false) (e1 : endpoint), P (ERec e0') e1 false) -> forall e0 e1 : endpoint, P e0 e1 (unfeq e0 e1).
Proof.
intros. apply unfeq_elim;eauto.
intros. split_and. rewrite /= list_eqP. eauto. 
Qed.*)

Let inE := NewSyntax.inE.


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
    eapply eguarded_shift in H1. erewrite H1 in H2. done. apply inject2.  done. 
    case_if. have : 0 = (0.: sigma >> succn ) 0. done. intros. rewrite {1}x in H2. 
    apply eguarded_shift in H2. rewrite H2 in H1. done. apply inject2. done. simpl in *. done.
(*    f_equal.  asimpl. apply inj_rem4'. intros. apply eguarded_fv2 in H1.  rewrite /= H1 in H3. 
    rewrite /= inE in H3.  rewrite /= (eqP H3). simpl in *. done.*)

    apply inject2.  done.
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
asimpl. apply inject2.  done. simpl in *. destruct x2; try done. simpl in *. inversion H1. subst. f_equal.  
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


(*
Fixpoint unfeq sigma e0 e1:= 
  match e0,e1 with 
  | EVar n0, EVar n1 => n0 == n1 
  | EEnd, EEnd => true
  | EMsg d0 c0 v0 e0', EMsg d1 c1 v1 e1' => (d0 == d1) && (c0 == c1) && (v0 == v1) && (unfeq sigma e0' e1')
  | EBranch d0 c0 es0, EBranch d1 c1 es1 => (d0 == d1) && (c0 == c1) && (list_eq (unfeq sigma) es0 es1)
  | ERec e0', _ => (if e1 is ERec e1' then unfeq ((var 0) : sigma) e0' e1' else false) || (unfeq n' (e0' [e (ERec e0').:ids]) e1)
  | _,_ => false  
end
else false.*)


Print endpoint. 


Require Import Coq.Program.Wf Program.
Print lt. 
(*Use equations because it supports nested well founded recursion*)




(*
(*from https://mattam82.github.io/Coq-Equations/examples/Examples.STLC.html
 just the definition of lexicografic*)

Require Import Arith Wf_nat.
Instance wf_nat : Classes.WellFounded lt := lt_wf.
Hint Constructors Subterm.lexprod : subterm_relation.

Derive Signature for Acc.
Notation lexicographic R S := (Subterm.lexprod _ _ R S).
*)


(*Fixpoint unfeq2 e0 e1 :=
match e0,e1 with
| EBranch d c es, EBranch d' c' es' => (d == d') || (c == c') || (list_eq unfeq2 es es')

 unfeq e0 e1 || unfeq e1 e0.

Definition unfeq2 e0 e1 := unfeq e0 e1 || unfeq e1 e0.*)


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





(*Lemma endpoint_rename : forall e,  endpoint_fv (ren_endpoint predn e) = predn @` endpoint_fv e.
Proof. 
elim;rewrite /=;intros. rewrite Imfset.imfsetE /=. fsetTac. rewrite seq_fsetE.
apply bool_iff. split. move/eqP=>->. rewrite map_f //=. rewrite !inE //=. 
move/mapP=>[]. intros. rewrite !inE in p. rewrite -(eqP p) -q //= eqxx //=.
simpl inrewrite predn_fset0 //=.
f_equal.*)

(*Lemma fv_shiftdown : forall e i, i \notin (endpoint_fv i e)  -> endpoint_fv i (shiftdown e) = endpoint_fv i.+1 e.
Proof. 
elim;rewrite /=;try done;intros.
move : H. rifliad;rewrite !inE;intros. all : try fsetTac. 
rewrite -H //=. asimpl.  rewrite /shiftdown.
 asimpl. f_equal. clear H0. clear H. rewrite /scons.
fext.  intros. 
Admitted.
*)

(*Lemma fv_predn : forall e, endpoint_fv e ⟨ predn ⟩ = [fset predn n | n in endpoint_fv e].
Proof. intros. fsetTac. destruct (k \in endpoint_fv e ⟨ predn ⟩) eqn:Heqn;rewrite Heqn /= bbrw.
apply/imfsetP.
elim : e k Heqn;intros.
- exists n. rewrite /= !inE //=. move : Heqn. rewrite /= !inE //=. lia.
- rewrite /= !inE //= in Heqn. 
- rewrite /= ?inE in Heqn.
  exists k. rewrite /=. move : Heqn. asimpl. move => HH.  
  have :  (k \in endpoint_fv e ⟨e predn ⟩). admit. move/H=>[]. move => x. simpl.
  intros. apply/imfsetP. exists x. simpl. rewrite !inE /=. split_and. 
  have : ( 0 .: predn >> succn ) = (0 .: id). fext. intros.  case. done. intros. simpl. destruct n. asimpl.  simpl. done.
asimpl_in Heqn. rewrite /= !inE //=. move : Heqn. rewrite /= !inE //=. lia.

 -
  elim;intros.
fsetTac. destruct (eqVneq k n.-1). rewrite bbrw.  
apply/imfsetP. exists n. simpl. rewrite !inE //=. done. 
rewrite bbrw.  move/imfsetP. move=>[] x. simpl. rewrite !inE. move/eqP=>->. lia. 
simpl. fsetTac. rewrite bbrw. move/imfsetP=>[] x. simpl. rewrite !inE //=.
fsetTac. asimpl.*)

(*Lemma subst_nop : forall e e' x, x \notin (fv e) -> subst_e x e e' = e. Proof. 
elim;rewrite /=;try done;intros. move : H. rewrite !inE.  rewrite neg_sym. move/negbTE=>->. done. 
move : H0. rewrite !inE. move/orP=>[]. by rewrite eq_sym=>->.  
intros. rifliad. rewrite H //=. 
f_equal. auto. f_equal. rewrite big_map in H0.  induction l. done. simpl. f_equal.  apply H.  rewrite !inE.  lia. simpl in H0. move : H0. 
rewrite big_cons. rewrite !inE. split_and. apply IHl. intros. apply H. rewrite !inE H1. lia. done. move : H0.  rewrite big_cons !inE. split_and. 
Qed.*)




(*Lemma fv_subst : forall  e e' n x, fv e' = fset0 -> n <> x -> (n \in (fv (subst_e x e e'))) = (n \in (fv e)).
Proof. elim;rewrite /=;try done;intros. rewrite !inE. rifliad. rewrite H !inE. have : n0 == n = false by lia. by move=>->. 
rewrite /= !inE. done. 
rifliad. rewrite /=. Check mem_map. Search (_ \in (map _ _)). Search _ (_ \in _ = _ \in _).  Search _ ((is_true _ -> is_true _) -> _ = _). rewrite !inE.  destruct (n0 != n)eqn:Heqn;rewrite /= //=.   rewrite Heqn //=.
apply H. done. done. rewrite Heqn //=. 
rewrite !big_map.  elim : l H. rewrite !big_nil. done. intros. rewrite !big_cons. rewrite !inE. rewrite H2 //=. 
destruct ( (n \in fv a)) eqn:Heqn; rewrite !Heqn //=. apply H. intros. apply H2. rewrite !inE H3. lia. done. done. 
Qed.*)

(*Lemma fv_nil_evar : forall e n, endpoint_fv 0 e = fset0 -> e <> EVar n. 
Proof.
elim;rewrite /=;try  done. intros. have : n \in [fset n]. by  rewrite !inE. move : H. have : n - 0 = n by lia. move=>->. move/fsetP=>->. done. 
Qed.

Lemma fset_nil : forall (A : choiceType) (n : A), [fset n] = fset0 -> False.
Proof. intros. move : H. move/fsetP=>HH. suff : n \in [fset n] = (n \in fset0). rewrite !inE eqxx //=. done. 
Qed.
*)
(*Lemma clean_up : forall e sigma, clean (endpoint_ren e S) [↑__endpoint sigma] = (clean e) [↑__endpoint sigma].*)

(*Lemma in_subst : forall e sigma, (endpoint_fv (e [e sigma])) = sigma @` (endpoint_fv e).*)


(*Lemma in_subst : forall v e n sigma, v \in (endpoint_fv e) ->  sigma v = EVar n ->  n \in (endpoint_fv (e [e sigma])). 
Proof. 
move => v e. elim : e v;asimpl;intros. rewrite !inE in H. rewrite -(eqP H) H0 //= !inE //=. 
rewrite !inE //= in H.
rewrite /endpoint_fv -/endpoint_fv. rewrite seq_fsetE. Search _ (_ \in pmap _ _). rewrite mem_pmap. apply/mapP.  exists v. 
move : H0. rewrite /endpoint_fv -/endpoint_fv.  rewrite seq_fsetE mem_pmap. move/mapP=>[]. intros. apply : H. eauto. 
destruct x. done.  simpl. asimpl. simpl in q. done. simpl. substify. asimpl.

move : H0. simpl. rewrite mem_map.
simpl. rewrite fsetE.*)

(*

asimpl. simpl. symmetry. case_if. rewrite -(eqP H2). 
  move : H1. destruct (clean e);rewrite /=;asimpl. destruct n.  done. simpl. asimpl. destruct (sigma n);rewrite /=;asimpl. 
  destruct n0. all : try done. rifliad. substify. move/eqP. rewrite /shiftdown. asimpl. move : H1. substify. asimpl. rewrite H. 
  

have :  subst_endpoint (scons (var 0) (sigma >> (⟨ ↑ ⟩ >> clean)))  == var 0 = false.

case_if. 
  simpl. case_if. move : H2. 
asimpl. rs. done.
- rs. case_if.  
 * rs. rewrite (eqP H1) /=. rifliad. rs. by rewrite /= eqxx. rewrite subst_nop //=. rewrite fv_clean. lia. 
 * rs. rewrite /= H //=.  rewrite fv_subst //=. symmetry. case_if.
  ** rs. rewrite (eqP H2) /=. rs. rewrite H1 eqxx. done.
  ** case_if.
   *** rs. rewrite /= H1. rifliad. exfalso. move : H4.  destruct (clean e);rewrite /=;rs. rifliad. move/eqP. apply : fv_nil_evar. 
       rewrite fv_clean //=. by rewrite H2. done. done. done. rifliad. 

   *** rs. rifliad. exfalso. move : H5. rewrite !inE H3. have : n != x by lia. move=>->. done. rewrite !inE H3.
       have : n != x by lia. move=>-> /=. rifliad. 
       destruct (clean e);rewrite /=;rs.  rifliad. rewrite (eqP H5) in H4. rs_in H4. rewrite eqxx in H4. rewrite -fv_clean in H0.  rewrite (eqP H4) in H0. rs_in H0. by apply fset_nil in H0. rs_in H4. rewrite H5 in H4. lia. done.
      all : try  by move : (eqP H4).   rs_in H4. rifliad. rs. f_equal. auto.  rs. f_equal. 
- rewrite -!map_comp. apply/eq_in_map. move => ll Hin /=. rewrite H //=.
Qed.

Lemma clean_subst : forall (e0 : endpoint)  e' x, endpoint_fv 0 e' = fset0 -> clean (e0[s e'//x]) = (clean e0)[s clean e'//x].
Proof.
elim;intros. 
- rs. rifliad.
- rs. done.
- rs. case_if.  
 * rs. rewrite (eqP H1) /=. rifliad. rs. by rewrite /= eqxx. rewrite subst_nop //=. rewrite fv_clean. lia. 
 * rs. rewrite /= H //=.  rewrite fv_subst //=. symmetry. case_if.
  ** rs. rewrite (eqP H2) /=. rs. rewrite H1 eqxx. done.
  ** case_if.
   *** rs. rewrite /= H1. rifliad. exfalso. move : H4.  destruct (clean e);rewrite /=;rs. rifliad. move/eqP. apply : fv_nil_evar. 
       rewrite fv_clean //=. by rewrite H2. done. done. done. rifliad. 

   *** rs. rifliad. exfalso. move : H5. rewrite !inE H3. have : n != x by lia. move=>->. done. rewrite !inE H3.
       have : n != x by lia. move=>-> /=. rifliad. 
       destruct (clean e);rewrite /=;rs.  rifliad. rewrite (eqP H5) in H4. rs_in H4. rewrite eqxx in H4. rewrite -fv_clean in H0.  rewrite (eqP H4) in H0. rs_in H0. by apply fset_nil in H0. rs_in H4. rewrite H5 in H4. lia. done.
      all : try  by move : (eqP H4).   rs_in H4. rifliad. rs. f_equal. auto.  rs. f_equal. 
- rewrite -!map_comp. apply/eq_in_map. move => ll Hin /=. rewrite H //=.
Qed.*)

(*Lemma rproject_subst : forall g g0 p i,  rproject (g[s g0//i]) p = (rproject g p)[s (rproject g0 p)//i].
Proof. elim;rewrite /=;try done;intros;rs. rifliad. rifliad. rewrite /=.  rewrite H. done.  
rifliad. simpl. rs. f_equal. done. simpl. rs. f_equal. done. 
rifliad. simpl. rs. f_equal. 
rewrite -!map_comp. apply/eq_in_map. move=>ll Hin. simpl. apply H.  done. 
simpl. rs.  f_equal.
rewrite -!map_comp. apply/eq_in_map. move=>ll Hin. simpl. apply H.  done. destruct l. done. simpl. apply H. rewrite !inE. done. 
Qed.*)

(*
Lemma fv_rename : forall e f, endpoint_fv e ⟨ f ⟩ = [fset f n | n in (endpoint_fv e)].
Proof.
elim;rewrite /=;intros. fsetTac. destruct (eqVneq k (f n));rewrite bbrw.
apply/imfsetP. exists n. rewrite /= !inE eqxx. done. done.
move/imfsetP=>[] x.  rewrite /= !inE. move/eqP=>->. lia.
rewrite predn_fset0 //=. asimpl. Print up_ren. 
fsetTac. symmetry. destruct ( (k \in f @` [fset n.-1 | n in endpoint_fv e & n != 0])) eqn:Heqn;rewrite Heqn bbrw.
move : Heqn. move/imfsetP=>[] x /= H' H2. subst.  move : H'. move/imfsetP=>[] x0 /=. rewrite !inE /=.
split_and. subst.  rewrite H. 
simpl. apply/imfsetP. exists x0. rewrite /= !inE H1  andbC /=. rewrite H. 
apply/imfsetP. exists x0. simpl. done. destruct x0.  done. simpl. have : f = predn. admit. move=>->. destruct x0. done. asimpl. simpl. move : H'.rewrite !inE. split_and.  exists x0.  done. rewrite H2 q. destruct x0. done. 
 simpl.  asimpl. admit.
done. simpl. asimpl. 
simpl in q. subst.  simpl.
Lemma fv_clean : forall e, endpoint_fv (clean e) = endpoint_fv e. 
Proof. elim;try solve [rewrite /=;try done];intros. 
rewrite /=. rifliad;simpl. 
fsetTac. rewrite (eqP H0) /= in H. rewrite -H.   rewrite bbrw. move/imfsetP=>[] x. simpl. rewrite !inE. split_and. lia.
rewrite H. done. fsetTac. 
rewrite H. fsetTac.

rewrite (eqP H0) in H. simpl. simpl in H. rewrite -H. simpl in H.
fsetTac. apply/negP/negP. move=>_. move/imfsetP=>[]. move => x. simpl. rewrite !inE. split_and. lia. done. 
rewrite /shiftdown.  *)












(*Fixpoint same_vars (e : endpoint ) :=
match e with 
| EBranch d c l => all (fun e' => endpoint_fv (nth EEnd l 0) == endpoint_fv e') l && (all same_vars l)
| EMsg _ _ _ e0 => same_vars e0
| ERec e0 => same_vars e0
| _ => true 
end.

Fixpoint same_varsg (e : gType ) :=
match e with 
| GBranch c l => all (fun e' => gType_fv (nth GEnd l 0) == gType_fv e') l && (all same_varsg l)
| GMsg _ _ e0 => same_varsg e0
| GRec e0 => same_varsg e0
| _ => true 
end.*)




(*Lemma in_foldr : forall l n,  n \in foldr (fun g' : gType => cat (fv_g g')) nil l ->  exists g, g \in l /\ n \in (fv_g g).
Proof. elim;try done;move => l n H n'.
rewrite /= mem_cat. move/orP=>[]. intros. exists l. rewrite !inE /= a. auto.
move/H. move=>[] x [].  intros. exists x. rewrite !inE a b. lia. Qed.*)

(*Lemma in_foldr2 : forall l n p g, g \in l -> n \in (fv (project  g p)) ->  n \in foldr (fun g' : gType => cat (fv (project g' p))) nil l.
Proof. elim;try done;intros. move : H0.
rewrite !inE. move/orP=>[]. move/eqP. intros. subst. simpl. rewrite mem_cat H1. done. intros.  simpl. rewrite mem_cat. apply/orP. right. apply : H. eauto. done. 
Qed.*)


(*
Lemma fv_project_in : forall g p n, lpreds rec_pred g ->  (n \in (fv_g g)) -> (n  \in (fv (project g p))).
Proof.
elim;rewrite //=;intros. move : H1. rewrite !inE.  split_and. apply (H p) in H3;last cc.
- rifliad. rewrite (eqP H1) in H3. simpl in H3. rewrite !inE in H3. lia. 
  simpl. Admitted. 
(*rewrite !inE.  split_and. 
- apply (H p) in H1;last cc. rifliad.
- rifliad. simpl. rewrite !big_map. 
  apply : big_cup_in.  intros. apply : H. done. cc. cc. apply/big_cup_in.  intros. apply : H4.  apply/big_cup_in. intros. apply : H4. rewrite big_map in H1. done. 
  rewrite /= !big_map.  apply : big_cup_in.  intros. apply : H. done. cc. eauto. rewrite big_map in H1. done. 
- rewrite match_n. apply H. cc. cc. move : H1. rewrite big_map foldr_exists. move/hasP=>[] x. intros. 
  intros.  move : p0. move/nthP=>Hnth. specialize Hnth with GEnd. destruct Hnth.

  apply : fv_rproject_in. 
  erewrite project_predP. apply : H. apply/mem_nth. apply : H1. cc. rewrite H4.  done. eauto.  cc.   all:cc. instantiate (1 := fresh a). rewrite /fresh. destruct (atom_fresh_for_list a). apply/negP.  move => HH. apply n0. destruct a. move : HH. rewrite !inE.  done. 
Qed.*)

Lemma fv_project_eq : forall g p n, lpreds rec_pred g ->  (n \in fv_g g) = (n \in fv (project g p)).
Proof. intros. destruct ( (n \in fv_g g)) eqn:Heqn. rewrite fv_project_in //=.
destruct ((n \in fv (project g p))) eqn:Heqn2. erewrite fv_rproject_in in Heqn. done. eauto. done. 
Qed.*)




