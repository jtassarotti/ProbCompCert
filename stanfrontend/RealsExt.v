Require Export RelationClasses Morphisms Utf8.
From mathcomp Require Import ssreflect ssrbool eqtype.
From Coquelicot Require Import Hierarchy Markov Rcomplements Rbar Lub Lim_seq SF_seq Continuity Hierarchy RInt RInt_analysis Derive.

Require Import Reals.
Require Import Coqlib.

Instance Rge_Transitive: Transitive Rge.
Proof. intros ???. eapply Rge_trans. Qed.
Instance Rle_Transitive: Transitive Rle.
Proof. intros ???. eapply Rle_trans. Qed.
Instance Rge_Reflexive: Reflexive Rge.
Proof. intros ?. eapply Rge_refl. Qed.
Instance Rle_Reflexive: Reflexive Rle.
Proof. intros ?. eapply Rle_refl. Qed.
Instance Rgt_Transitive: Transitive Rgt.
Proof. intros ???. eapply Rgt_trans. Qed.
Instance Rlt_Transitive: Transitive Rlt.
Proof. intros ???. eapply Rlt_trans. Qed.

Import Rbar.
Instance Rbar_le_Transitive: Transitive Rbar_le.
Proof. intros ???. eapply Rbar_le_trans. Qed.
Instance Rbar_le_Reflexive: Reflexive Rbar_le.
Proof. intros ?. eapply Rbar_le_refl. Qed.
Instance Rbar_lt_Transitive: Transitive Rbar_lt.
Proof. intros ???. eapply Rbar_lt_trans. Qed.

Instance ge_Transitive: Transitive ge.
Proof. intros ???. auto with *. Qed.
Instance le_Transitive: Transitive le.
Proof. intros ???. auto with *. Qed.
Instance ge_Reflexive: Reflexive ge.
Proof. intros ?. auto with *. Qed.
Instance le_Reflexive: Reflexive le.
Proof. intros ?. auto with *. Qed.
Instance gt_Transitive: Transitive gt.
Proof. intros ???. auto with *. Qed.
Instance lt_Transitive: Transitive lt.
Proof. intros ???. auto with *. Qed.

(* To be compatible with ssreflect in various ways it's nice to make R
   into an eqType *)

Definition R_eqP : Equality.axiom (fun x y: R => Req_EM_T x y).
Proof. move => x y. apply sumboolP. Qed.

Canonical R_eqMixin := EqMixin R_eqP.
Canonical R_eqType := Eval hnf in EqType R R_eqMixin.

Require Import Psatz.
Instance Rlt_plus_proper: Proper (Rlt ==> Rlt ==> Rlt) Rplus.
Proof.
  intros ?? Hle ?? Hle'. apply Rplus_lt_compat; auto.
Qed.
Instance Rlt_plus_proper': Proper (Rlt ==> eq ==> Rlt) Rplus.
Proof.
  intros ?? Hle ?? Hle'. subst. nra.
Qed.
Instance Rlt_plus_proper'': Proper (Rlt ==> Rle ==> Rlt) Rplus.
Proof.
  intros ?? Hle ?? Hle'. subst. nra.
Qed.

Instance Rle_plus_proper_left: Proper (Rle ==> eq ==> Rle) Rplus.
Proof. intros ?? Hle ?? Hle'. nra. Qed.
Instance Rle_plus_proper_right: Proper (eq ==> Rle ==> Rle) Rplus.
Proof. intros ?? Hle ?? Hle'. nra. Qed.
Instance Rle_plus_proper: Proper (Rle ==> Rle ==> Rle) Rplus.
Proof. intros ?? Hle ?? Hle'. nra. Qed.


Lemma Rmax_INR a b: Rmax (INR a) (INR b) = INR (max a b).
Proof.
  apply Rmax_case_strong; intros ?%INR_le; f_equal;
    [ rewrite Max.max_l // | rewrite Max.max_r //].
Qed.

Definition Rbar_max (x y: Rbar) : Rbar :=
  match x, y with
  | Finite x', Finite y' => Rmax x' y'
  | m_infty, _ => y
  | _, m_infty => x
  | p_infty, _ => p_infty
  | _, p_infty => p_infty
  end.

Lemma Rbar_max_l: ∀ x y : Rbar, Rbar_le x (Rbar_max x y).
Proof.
  destruct x, y => //=; try apply Rmax_l; reflexivity.
Qed.

Lemma Rbar_max_r: ∀ x y : Rbar, Rbar_le y (Rbar_max x y).
  destruct x, y => //=; try apply Rmax_r; reflexivity.
Qed.

Lemma Rbar_max_comm: ∀ x y : Rbar, Rbar_max x y = Rbar_max y x.
Proof. destruct x, y => //=; by rewrite Rmax_comm. Qed.

Lemma Rbar_max_case: ∀ (x y : Rbar) (P : Rbar → Type), P x → P y → P (Rbar_max x y).
Proof. destruct x, y => //=; by apply Rmax_case. Qed.

Lemma Rbar_max_case_strong:
  ∀ (x y : Rbar) (P : Rbar → Type),
  (Rbar_le y x → P x) → (Rbar_le x y → P y) → P (Rbar_max x y).
Proof. destruct x, y => //=; try apply Rmax_case_strong; eauto. Qed.

Definition Rbar_min (x y: Rbar) : Rbar :=
  match x, y with
  | Finite x', Finite y' => Rmin x' y'
  | m_infty, _ => m_infty
  | _, m_infty => m_infty
  | p_infty, _ => y
  | _, p_infty => x
  end.

Lemma Rbar_min_l: ∀ x y : Rbar, Rbar_le (Rbar_min x y) x.
Proof.
  destruct x, y => //=; try apply Rmin_l; reflexivity.
Qed.

Lemma Rbar_min_r: ∀ x y : Rbar, Rbar_le (Rbar_min x y) y.
  destruct x, y => //=; try apply Rmin_r; reflexivity.
Qed.

Lemma Rbar_min_comm: ∀ x y : Rbar, Rbar_min x y = Rbar_min y x.
Proof. destruct x, y => //=; by rewrite Rmin_comm. Qed.

Lemma Rbar_min_case: ∀ (x y : Rbar) (P : Rbar → Type), P x → P y → P (Rbar_min x y).
Proof. destruct x, y => //=; by apply Rmin_case. Qed.

Lemma Rbar_min_case_strong:
  ∀ (x y : Rbar) (P : Rbar → Type),
  (Rbar_le x y → P x) → (Rbar_le y x → P y) → P (Rbar_min x y).
Proof. destruct x, y => //=; try apply Rmin_case_strong; eauto. Qed.

Lemma norm_Rabs r: norm r = Rabs r.
Proof.
  rewrite /norm//=/abs.
Qed.

Lemma Rabs_case r (P : R -> Type):
  (0 <= r -> P r) -> (0 <= -r -> P (-r)) -> P (Rabs r).
Proof.
  intros Hcase1 Hcase2.
  destruct (Rle_dec 0 r) as [?|?%Rnot_le_gt].
  * rewrite Rabs_right //=; eauto; try nra.
  * rewrite Rabs_left1 //=.
    ** eapply Hcase2. apply Ropp_le_cancel.
       rewrite Ropp_0 Ropp_involutive. left. auto.
    ** left. auto.
Qed.

Lemma is_lim_unique': forall (f : R -> R) (x l1 l2 : Rbar), is_lim f x l1 -> is_lim f x l2 -> l1 = l2.
Proof.
  intros f x l1 l2 Hlim1%is_lim_unique Hlim2%is_lim_unique; congruence.
Qed.

Lemma is_lim_unique'_R: forall (f : R -> R) (x l1 l2 : R), is_lim f x l1 -> is_lim f x l2 -> l1 = l2.
Proof.
  intros f x l1 l2 Hlim1%is_lim_unique Hlim2%is_lim_unique; congruence.
Qed.

Lemma eps_squeeze_between a b (eps : posreal) :
  a < b ->
  exists (eps': posreal), eps' <= eps ∧ forall y, abs (minus y b) < eps' -> a <= y <= b + eps.
Proof.
  intros Hlt1.
  assert (Hpos: 0 < b - a).
  { nra. }
  destruct (Rle_dec eps (b - a)).
  * exists eps. split; first nra. intros y.
    rewrite /abs/minus/plus/opp//=.
    apply Rabs_case; nra.
  * exists (mkposreal (b - a) Hpos). split.
    { simpl. nra. }
    intros y.
    rewrite /abs/minus/plus/opp//=.
    apply Rabs_case; nra.
Qed.

Lemma eps_squeeze_between' a b (eps : posreal) :
  a < b ->
  exists (eps': posreal), eps' <= eps ∧ forall y, abs (minus y a) < eps' -> a - eps <= y <= b.
Proof.
  intros Hlt1.
  assert (Hpos: 0 < b - a).
  { nra. }
  destruct (Rle_dec eps (b - a)).
  * exists eps. split; first nra. intros y.
    rewrite /abs/minus/plus/opp//=.
    apply Rabs_case; nra.
  * exists (mkposreal (b - a) Hpos). split.
    { simpl. nra. }
    intros y.
    rewrite /abs/minus/plus/opp//=.
    apply Rabs_case; nra.
Qed.

Lemma is_lim_continuity':
  ∀ (f : R → R) (x : R), continuous f x → is_lim f x (f x).
Proof.
  intros f x Hcont.
  apply (is_lim_comp_continuous (λ x, x) f); auto.
  apply: is_lim_id.
Qed.

Lemma filterlim_Rbar_opp' :
  forall x,
  filterlim Ropp (Rbar_locally' x) (Rbar_locally' (Rbar_opp x)).
Proof.
intros [x| |] P [eps He].
- exists eps.
  intros y Hy Hneq.
  apply He.
  rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /=.
  by rewrite Ropp_involutive Rplus_comm Rabs_minus_sym.
  nra.
- exists (-eps).
  intros y Hy.
  apply He.
  apply Ropp_lt_cancel.
  by rewrite Ropp_involutive.
- exists (-eps).
  intros y Hy.
  apply He.
  apply Ropp_lt_cancel.
  by rewrite Ropp_involutive.
Qed.

Definition Rbar_left_loc_seq (x : Rbar) (n : nat) := match x with
    | Finite x => x - / (INR n + 1)
    | p_infty => INR n
    | m_infty => - INR n
  end.

Lemma Rbar_left_loc_seq_finite_spec (x: R) (n : nat) :
  Rbar_left_loc_seq x n = Ropp (Rbar_loc_seq (Ropp x) n).
Proof. simpl. nra. Qed.

Lemma filterlim_Rbar_left_loc_seq :
  forall x, filterlim (Rbar_left_loc_seq x) Hierarchy.eventually (Rbar_locally' x).
Proof.
  intros x. destruct x.
  - eapply filterlim_ext.
    { intros. symmetry. apply Rbar_left_loc_seq_finite_spec. }
    {  assert (Finite r = (Rbar_opp (Rbar_opp (Finite r)))) as Heq.
       { simpl. f_equal. nra. }
       apply: filterlim_comp.
       { eapply filterlim_Rbar_loc_seq. }
       { rewrite Heq. apply filterlim_Rbar_opp'. }
    }
  - apply filterlim_Rbar_loc_seq.
  - apply filterlim_Rbar_loc_seq.
Qed.

Lemma is_lim_seq_Rbar_left_loc_seq (x : Rbar) :
  is_lim_seq (Rbar_left_loc_seq x) x.
Proof.
  intros P HP.
  apply filterlim_Rbar_left_loc_seq.
  now apply Rbar_locally'_le.
Qed.

Definition Rbar_at_left (x: Rbar) := within (λ u : Rbar, Rbar_lt u x) (Rbar_locally x).
Definition Rbar_at_right (x: Rbar) := within (λ u : Rbar, Rbar_lt x u) (Rbar_locally x).

Lemma filterlim_Rbar_left_loc_seq' :
  forall x, x <> m_infty -> filterlim (Rbar_left_loc_seq x) Hierarchy.eventually (Rbar_at_left x).
Proof.
  intros x Hnm. specialize (filterlim_Rbar_left_loc_seq x).
  intros Hlim.
  eapply filterlim_filter_le_2 in Hlim; last first.
  { apply Rbar_locally'_le. }
  move: Hlim.
  unfold filterlim, filter_le, filtermap.
  intros Hlim P HP.
  specialize (Hlim (λ y, P y ∨ Rbar_le x y)).
  destruct Hlim as (N&HN).
  { unfold Rbar_at_left in HP.
    unfold within in HP.
    move: HP.
    apply: filter_imp. intros r Hy.
    destruct (Rbar_lt_dec r x).
    { left. eauto. }
    { right. apply Rbar_not_lt_le; auto. }
  }
  exists N. intros. edestruct (HN n) as [?|Hbad]; eauto.
  exfalso. destruct x; auto; try congruence.
  eapply Rbar_lt_not_le; eauto.
  simpl.
  apply tech_Rgt_minus, RinvN_pos.
Qed.

Lemma filterlim_Rbar_loc_seq' :
  forall x, x <> p_infty -> filterlim (Rbar_loc_seq x) Hierarchy.eventually (Rbar_at_right x).
Proof.
  intros x Hnm. specialize (filterlim_Rbar_loc_seq x).
  intros Hlim.
  eapply filterlim_filter_le_2 in Hlim; last first.
  { apply Rbar_locally'_le. }
  move: Hlim.
  unfold filterlim, filter_le, filtermap.
  intros Hlim P HP.
  specialize (Hlim (λ y, P y ∨ Rbar_le y x)).
  destruct Hlim as (N&HN).
  { unfold Rbar_at_right in HP.
    unfold within in HP.
    move: HP.
    apply: filter_imp. intros r Hy.
    destruct (Rbar_lt_dec x r).
    { left. eauto. }
    { right. apply Rbar_not_lt_le; auto. }
  }
  exists N. intros. edestruct (HN n) as [?|Hbad]; eauto.
  exfalso. destruct x; auto; try congruence.
  eapply Rbar_lt_not_le; eauto.
  simpl.
  cut (0 < / (INR n + 1)).
  { nra. }
  apply RinvN_pos.
Qed.

Definition is_left_lim (f : R -> R) (x l : Rbar) :=
  x ≠ m_infty ∧ filterlim f (Rbar_at_left x) (Rbar_locally l).

Definition is_right_lim (f : R -> R) (x l : Rbar) :=
  x ≠ p_infty ∧ filterlim f (Rbar_at_right x) (Rbar_locally l).

Definition is_left_lim' (f : R -> R) (x l : Rbar) :=
  x ≠ m_infty ∧
  match l with
    | Finite l =>
      forall eps : posreal, Rbar_at_left x (fun y => Rabs (f y - l) < eps)
    | p_infty => forall M : R, Rbar_at_left x (fun y => M < f y)
    | m_infty => forall M : R, Rbar_at_left x (fun y => f y < M)
  end.
Definition ex_left_lim (f : R -> R) (x : Rbar) := exists l : Rbar, is_left_lim f x l.
Definition ex_finite_left_lim (f : R -> R) (x : Rbar) := exists l : R, is_left_lim f x l.
Definition LeftLim (f : R -> R) (x : Rbar) := Lim_seq (fun n => f (Rbar_left_loc_seq x n)).

Definition is_right_lim' (f : R -> R) (x l : Rbar) :=
  x ≠ p_infty ∧
  match l with
    | Finite l =>
      forall eps : posreal, Rbar_at_right x (fun y => Rabs (f y - l) < eps)
    | p_infty => forall M : R, Rbar_at_right x (fun y => M < f y)
    | m_infty => forall M : R, Rbar_at_right x (fun y => f y < M)
  end.
Definition ex_right_lim (f : R -> R) (x : Rbar) := exists l : Rbar, is_right_lim f x l.
Definition ex_finite_right_lim (f : R -> R) (x : Rbar) := exists l : R, is_right_lim f x l.
Definition RightLim (f : R -> R) (x : Rbar) := Lim_seq (fun n => f (Rbar_loc_seq x n)).

(* Exactly the same proof script as is_lim_spec from Coquelicot *)
Lemma is_left_lim_spec :
  forall f x l,
  is_left_lim' f x l <-> is_left_lim f x l.
Proof.
destruct l as [l| |] ; split.
- intros (?&H); split; first done. intros P [eps LP].
  unfold filtermap.
  generalize (H eps).
  apply filter_imp.
  intros u.
  apply LP.
- intros (?&H); split; first done. intros eps.
  apply (H (fun y => Rabs (y - l) < eps)).
  now exists eps.
- intros (?&H); split; first done. intros P [M LP].
  unfold filtermap.
  generalize (H M).
  apply filter_imp.
  intros u.
  apply LP.
- intros (?&H); split; first done.
  intros M.
  apply (H (fun y => M < y)).
  now exists M.
- intros (?&H); split; first done. intros P [M LP].
  unfold filtermap.
  generalize (H M).
  apply filter_imp.
  intros u.
  apply LP.
- intros (?&H); split; first done.
  intros M.
  apply (H (fun y => y < M)).
  now exists M.
Qed.

Lemma is_right_lim_spec :
  forall f x l,
  is_right_lim' f x l <-> is_right_lim f x l.
Proof.
destruct l as [l| |] ; split.
- intros (?&H); split; first done. intros P [eps LP].
  unfold filtermap.
  generalize (H eps).
  apply filter_imp.
  intros u.
  apply LP.
- intros (?&H); split; first done. intros eps.
  apply (H (fun y => Rabs (y - l) < eps)).
  now exists eps.
- intros (?&H); split; first done. intros P [M LP].
  unfold filtermap.
  generalize (H M).
  apply filter_imp.
  intros u.
  apply LP.
- intros (?&H); split; first done.
  intros M.
  apply (H (fun y => M < y)).
  now exists M.
- intros (?&H); split; first done. intros P [M LP].
  unfold filtermap.
  generalize (H M).
  apply filter_imp.
  intros u.
  apply LP.
- intros (?&H); split; first done.
  intros M.
  apply (H (fun y => y < M)).
  now exists M.
Qed.

Lemma is_left_lim_comp' :
  forall {T} {F} {FF : @Filter T F} (f : T -> R) (g : R -> R) (x l : Rbar),
  filterlim f F (Rbar_at_left x) -> is_left_lim g x l ->
  F (fun y => Rbar_lt (Finite (f y)) x) ->
  filterlim (fun y => g (f y)) F (Rbar_locally l).
Proof.
intros T F FF f g x l Lf (?&Lg) Hf.
revert Lg.
apply filterlim_comp.
intros P HP.
by apply Lf.
Qed.

Lemma is_right_lim_comp' :
  forall {T} {F} {FF : @Filter T F} (f : T -> R) (g : R -> R) (x l : Rbar),
  filterlim f F (Rbar_at_right x) -> is_right_lim g x l ->
  F (fun y => Rbar_lt x (Finite (f y))) ->
  filterlim (fun y => g (f y)) F (Rbar_locally l).
Proof.
intros T F FF f g x l Lf (?&Lg) Hf.
revert Lg.
apply filterlim_comp.
intros P HP.
by apply Lf.
Qed.

Lemma is_left_lim_comp_seq (f : R -> R) (u : nat -> R) (x l : Rbar) :
  is_left_lim f x l ->
  Hierarchy.eventually (fun n => Rbar_lt (Finite (u n)) x) ->
  is_lim_seq u x -> is_lim_seq (fun n => f (u n)) l.
Proof.
intros Lf Hu Lu.
eapply is_left_lim_comp'; eauto.
unfold is_lim_seq in Lu.
move: Hu Lu. unfold filterlim.
unfold filter_le.
unfold filtermap, Hierarchy.eventually.
intros Heventually Hu P Hleft.
specialize (Hu (λ y, P y ∨ Rbar_le x y)).
destruct Hu as (N&HN).
{ unfold Rbar_at_left in Hleft.
  unfold within in Hleft.
  move: Hleft.
  apply: filter_imp. intros r Hy.
  destruct (Rbar_lt_dec r x).
  { left. eauto. }
  { right. apply Rbar_not_lt_le; auto. }
}
destruct (Heventually) as (N'&HN').
exists (max N N').
intros n Hle.
exploit (HN n).
{ eapply Max.max_lub_l; eauto. }
exploit (HN' n).
{ eapply Max.max_lub_r; eauto. }
intros Hlt [|Hle']; auto. exfalso.
eapply Rbar_lt_not_le; eauto.
Qed.

Lemma is_right_lim_comp_seq (f : R -> R) (u : nat -> R) (x l : Rbar) :
  is_right_lim f x l ->
  Hierarchy.eventually (fun n => Rbar_lt x (Finite (u n))) ->
  is_lim_seq u x -> is_lim_seq (fun n => f (u n)) l.
Proof.
intros Lf Hu Lu.
eapply is_right_lim_comp'; eauto.
unfold is_lim_seq in Lu.
move: Hu Lu. unfold filterlim.
unfold filter_le.
unfold filtermap, Hierarchy.eventually.
intros Heventually Hu P Hleft.
specialize (Hu (λ y, P y ∨ Rbar_le y x)).
destruct Hu as (N&HN).
{ unfold Rbar_at_right in Hleft.
  unfold within in Hleft.
  move: Hleft.
  apply: filter_imp. intros r Hy.
  destruct (Rbar_lt_dec x r).
  { left. eauto. }
  { right. apply Rbar_not_lt_le; auto. }
}
destruct (Heventually) as (N'&HN').
exists (max N N').
intros n Hle.
exploit (HN n).
{ eapply Max.max_lub_l; eauto. }
exploit (HN' n).
{ eapply Max.max_lub_r; eauto. }
intros Hlt [|Hle']; auto. exfalso.
eapply Rbar_lt_not_le; eauto.
Qed.

(** Uniqueness *)

Lemma is_left_lim_non_m_infty (f : R -> R) (x l : Rbar):
  is_left_lim f x l -> x ≠ m_infty.
Proof. destruct 1; auto. Qed.

Lemma is_right_lim_non_p_infty (f : R -> R) (x l : Rbar):
  is_right_lim f x l -> x ≠ p_infty.
Proof. destruct 1; auto. Qed.

Lemma is_left_lim_unique (f : R -> R) (x l : Rbar) :
  is_left_lim f x l -> LeftLim f x = l.
Proof.
  intros Hlim.
  specialize (is_left_lim_non_m_infty f x l Hlim) => ?.
  unfold LeftLim.
  rewrite (is_lim_seq_unique _ l) //.
  apply (is_left_lim_comp_seq f _ x l Hlim); last first.
  { apply is_lim_seq_Rbar_left_loc_seq. }
  exists 1%nat => n Hn.
  destruct Hlim as (?&Hlim).
  destruct x as [x | | ] => //=.
  apply Rgt_lt, tech_Rgt_minus.
  by apply RinvN_pos.
Qed.

Lemma is_right_lim_unique (f : R -> R) (x l : Rbar) :
  is_right_lim f x l -> RightLim f x = l.
Proof.
  intros Hlim.
  specialize (is_right_lim_non_p_infty f x l Hlim) => ?.
  unfold RightLim.
  rewrite (is_lim_seq_unique _ l) //.
  apply (is_right_lim_comp_seq f _ x l Hlim); last first.
  { apply is_lim_seq_Rbar_loc_seq. }
  exists 1%nat => n Hn.
  destruct Hlim as (?&Hlim).
  destruct x as [x | | ] => //=.
  specialize (RinvN_pos n). nra.
Qed.

Lemma LeftLim_correct (f : R -> R) (x : Rbar) :
  ex_left_lim f x -> is_left_lim f x (LeftLim f x).
Proof.
  intros (l,H).
  replace (LeftLim f x) with l.
    apply H.
  apply sym_eq, is_left_lim_unique, H.
Qed.

Lemma RightLim_correct (f : R -> R) (x : Rbar) :
  ex_right_lim f x -> is_right_lim f x (RightLim f x).
Proof.
  intros (l,H).
  replace (RightLim f x) with l.
    apply H.
  apply sym_eq, is_right_lim_unique, H.
Qed.

Lemma ex_finite_left_lim_correct (f : R -> R) (x : Rbar) :
  ex_finite_left_lim f x <-> ex_left_lim f x /\ is_finite (LeftLim f x).
Proof.
  split.
  case => l Hf.
  move: (is_left_lim_unique f x l Hf) => Hf0.
  split.
  by exists l.
  by rewrite Hf0.
  case ; case => l Hf Hf0.
  exists (real l).
  rewrite -(is_left_lim_unique _ _ _ Hf).
  rewrite Hf0.
  by rewrite (is_left_lim_unique _ _ _ Hf).
Qed.
Lemma LeftLim_correct' (f : R -> R) (x : Rbar) :
  ex_finite_left_lim f x -> is_left_lim f x (real (LeftLim f x)).
Proof.
  intro Hf.
  apply ex_finite_left_lim_correct in Hf.
  rewrite (proj2 Hf).
  by apply LeftLim_correct, Hf.
Qed.

Lemma ex_finite_right_lim_correct (f : R -> R) (x : Rbar) :
  ex_finite_right_lim f x <-> ex_right_lim f x /\ is_finite (RightLim f x).
Proof.
  split.
  case => l Hf.
  move: (is_right_lim_unique f x l Hf) => Hf0.
  split.
  by exists l.
  by rewrite Hf0.
  case ; case => l Hf Hf0.
  exists (real l).
  rewrite -(is_right_lim_unique _ _ _ Hf).
  rewrite Hf0.
  by rewrite (is_right_lim_unique _ _ _ Hf).
Qed.
Lemma RightLim_correct' (f : R -> R) (x : Rbar) :
  ex_finite_right_lim f x -> is_right_lim f x (real (RightLim f x)).
Proof.
  intro Hf.
  apply ex_finite_right_lim_correct in Hf.
  rewrite (proj2 Hf).
  by apply RightLim_correct, Hf.
Qed.

(** ** Operations and order *)

(** Extensionality *)

Lemma is_left_lim_ext_loc (f g : R -> R) (x l : Rbar) :
  Rbar_at_left x (fun y => f y = g y)
  -> is_left_lim f x l -> is_left_lim g x l.
Proof.
  intros Hatleft (?&Hlim).
  split; first done. move: Hatleft Hlim.
  apply: filterlim_ext_loc.
Qed.
Lemma ex_left_lim_ext_loc (f g : R -> R) (x : Rbar) :
  Rbar_at_left x (fun y => f y = g y)
  -> ex_left_lim f x -> ex_left_lim g x.
Proof.
  move => H [l Hf].
  exists l.
  by apply is_left_lim_ext_loc with f.
Qed.
Lemma LeftLim_ext_loc (f g : R -> R) (x : Rbar) :
  x <> m_infty ->
  Rbar_at_left x (fun y => f y = g y)
  -> LeftLim g x = LeftLim f x.
Proof.
  move => Hneq H.
  apply sym_eq.
  apply Lim_seq_ext_loc.
  eapply (filterlim_Rbar_left_loc_seq' _ Hneq (λ y, f y = g y) H).
Qed.

Lemma is_left_lim_ext (f g : R -> R) (x l : Rbar) :
  (forall y, f y = g y)
  -> is_left_lim f x l -> is_left_lim g x l.
Proof.
  move => H.
  apply is_left_lim_ext_loc.
  by apply filter_forall.
Qed.
Lemma ex_left_lim_ext (f g : R -> R) (x : Rbar) :
  (forall y, f y = g y)
  -> ex_left_lim f x -> ex_left_lim g x.
Proof.
  move => H [l Hf].
  exists l.
  by apply is_left_lim_ext with f.
Qed.
Lemma LeftLim_ext (f g : R -> R) (x : Rbar) :
  (forall y, f y = g y)
  -> LeftLim g x = LeftLim f x.
Proof.
  move => H.
  apply sym_eq.
  apply Lim_seq_ext_loc.
  by apply filter_forall.
Qed.

Lemma is_right_lim_ext_loc (f g : R -> R) (x l : Rbar) :
  Rbar_at_right x (fun y => f y = g y)
  -> is_right_lim f x l -> is_right_lim g x l.
Proof.
  intros Hatright (?&Hlim).
  split; first done. move: Hatright Hlim.
  apply: filterlim_ext_loc.
Qed.
Lemma ex_right_lim_ext_loc (f g : R -> R) (x : Rbar) :
  Rbar_at_right x (fun y => f y = g y)
  -> ex_right_lim f x -> ex_right_lim g x.
Proof.
  move => H [l Hf].
  exists l.
  by apply is_right_lim_ext_loc with f.
Qed.
Lemma RightLim_ext_loc (f g : R -> R) (x : Rbar) :
  x <> p_infty ->
  Rbar_at_right x (fun y => f y = g y)
  -> RightLim g x = RightLim f x.
Proof.
  move => Hneq H.
  apply sym_eq.
  apply Lim_seq_ext_loc.
  eapply (filterlim_Rbar_loc_seq' _ Hneq (λ y, f y = g y) H).
Qed.

Lemma is_right_lim_ext (f g : R -> R) (x l : Rbar) :
  (forall y, f y = g y)
  -> is_right_lim f x l -> is_right_lim g x l.
Proof.
  move => H.
  apply is_right_lim_ext_loc.
  by apply filter_forall.
Qed.
Lemma ex_right_lim_ext (f g : R -> R) (x : Rbar) :
  (forall y, f y = g y)
  -> ex_right_lim f x -> ex_right_lim g x.
Proof.
  move => H [l Hf].
  exists l.
  by apply is_right_lim_ext with f.
Qed.
Lemma RightLim_ext (f g : R -> R) (x : Rbar) :
  (forall y, f y = g y)
  -> RightLim g x = RightLim f x.
Proof.
  move => H.
  apply sym_eq.
  apply Lim_seq_ext_loc.
  by apply filter_forall.
Qed.

(** Composition *)

Lemma is_left_lim_comp (f g : R -> R) (x k l : Rbar) :
  is_left_lim f l k -> is_left_lim g x l -> Rbar_at_left x (fun y => Rbar_lt (g y) l)
    -> is_left_lim (fun x => f (g x)) x k.
Proof.
  intros (?&Lf) (?&Lg) Hg.
  split; auto.
  eapply (is_left_lim_comp' g f l k); auto; last first.
  { split; auto. }
  move: Lg Hg. unfold filterlim, filter_le, filtermap, Rbar_at_left, within. intros Lg Hg P HP.
  specialize (Lg _ HP). specialize (filter_and _ _ Lg Hg) as Hand.
  clear Lg Hg. eapply filter_imp; eauto. simpl. intros x' (HP1&HP2) Hlt.
  destruct x; try congruence.
  { destruct l; try congruence; intuition. }
  { destruct l; try congruence; intuition. }
Qed.

Lemma ex_left_lim_comp (f g : R -> R) (x : Rbar) :
  ex_left_lim f (LeftLim g x) -> ex_left_lim g x -> Rbar_at_left x (fun y => Rbar_lt (g y) (LeftLim g x))
    -> ex_left_lim (fun x => f (g x)) x.
Proof.
  intros.
  exists (LeftLim f (LeftLim g x)).
  apply is_left_lim_comp with (LeftLim g x).
  by apply LeftLim_correct.
  by apply LeftLim_correct.
  by apply H1.
Qed.
Lemma LeftLim_comp (f g : R -> R) (x : Rbar) :
  ex_left_lim f (LeftLim g x) -> ex_left_lim g x -> Rbar_at_left x (fun y => Rbar_lt (g y) (LeftLim g x))
    -> LeftLim (fun x => f (g x)) x = LeftLim f (LeftLim g x).
Proof.
  intros.
  apply is_left_lim_unique.
  apply is_left_lim_comp with (LeftLim g x).
  by apply LeftLim_correct.
  by apply LeftLim_correct.
  by apply H1.
Qed.

Lemma is_right_lim_comp (f g : R -> R) (x k l : Rbar) :
  is_right_lim f l k -> is_right_lim g x l -> Rbar_at_right x (fun y => Rbar_lt l (g y))
    -> is_right_lim (fun x => f (g x)) x k.
Proof.
  intros (?&Lf) (?&Lg) Hg.
  split; auto.
  eapply (is_right_lim_comp' g f l k); auto; last first.
  { split; auto. }
  move: Lg Hg. unfold filterlim, filter_le, filtermap, Rbar_at_right, within. intros Lg Hg P HP.
  specialize (Lg _ HP). specialize (filter_and _ _ Lg Hg) as Hand.
  clear Lg Hg. eapply filter_imp; eauto. simpl. intros x' (HP1&HP2) Hlt.
  destruct x; try congruence.
  { destruct l; try congruence; intuition. }
  { destruct l; try congruence; intuition. }
Qed.

Lemma ex_right_lim_comp (f g : R -> R) (x : Rbar) :
  ex_right_lim f (RightLim g x) -> ex_right_lim g x -> Rbar_at_right x (fun y => Rbar_lt (RightLim g x) (g y))
    -> ex_right_lim (fun x => f (g x)) x.
Proof.
  intros.
  exists (RightLim f (RightLim g x)).
  apply is_right_lim_comp with (RightLim g x).
  by apply RightLim_correct.
  by apply RightLim_correct.
  by apply H1.
Qed.
Lemma RightLim_comp (f g : R -> R) (x : Rbar) :
  ex_right_lim f (RightLim g x) -> ex_right_lim g x -> Rbar_at_right x (fun y => Rbar_lt (RightLim g x) (g y))
    -> RightLim (fun x => f (g x)) x = RightLim f (RightLim g x).
Proof.
  intros.
  apply is_right_lim_unique.
  apply is_right_lim_comp with (RightLim g x).
  by apply RightLim_correct.
  by apply RightLim_correct.
  by apply H1.
Qed.

Lemma is_left_lim_const (a : R) (x : Rbar) :
  x <> m_infty ->
  is_left_lim (fun _ => a) x a.
Proof.
  split; auto. intros P HP.
now apply filterlim_const.
Qed.
Lemma ex_left_lim_const (a : R) (x : Rbar) :
  x <> m_infty ->
  ex_left_lim (fun _ => a) x.
Proof.
  exists a.
  by apply is_left_lim_const.
Qed.
Lemma LeftLim_const (a : R) (x : Rbar) :
  x <> m_infty ->
  LeftLim (fun _ => a) x = a.
Proof.
  intros. apply is_left_lim_unique.
  by apply is_left_lim_const.
Qed.

Lemma is_right_lim_const (a : R) (x : Rbar) :
  x <> p_infty ->
  is_right_lim (fun _ => a) x a.
Proof.
  split; auto. intros P HP.
now apply filterlim_const.
Qed.
Lemma ex_right_lim_const (a : R) (x : Rbar) :
  x <> p_infty ->
  ex_right_lim (fun _ => a) x.
Proof.
  exists a.
  by apply is_right_lim_const.
Qed.
Lemma RightLim_const (a : R) (x : Rbar) :
  x <> p_infty ->
  RightLim (fun _ => a) x = a.
Proof.
  intros. apply is_right_lim_unique.
  by apply is_right_lim_const.
Qed.

(** Addition *)

Lemma is_left_lim_plus (f g : R -> R) (x lf lg l : Rbar) :
  is_left_lim f x lf -> is_left_lim g x lg ->
  is_Rbar_plus lf lg l ->
  is_left_lim (fun y => f y + g y) x l.
Proof.
intros (?&Cf) (?&Cg) Hp.
split; auto.
eapply filterlim_comp_2 ; try eassumption.
by apply filterlim_Rbar_plus.
Qed.
Lemma is_left_lim_plus' (f g : R -> R) (x : Rbar) (lf lg : R) :
  is_left_lim f x lf -> is_left_lim g x lg ->
  is_left_lim (fun y => f y + g y) x (lf + lg).
Proof.
  intros Hf Hg.
  eapply is_left_lim_plus.
  by apply Hf.
  by apply Hg.
  by [].
Qed.
Lemma ex_left_lim_plus (f g : R -> R) (x : Rbar) :
  ex_left_lim f x -> ex_left_lim g x ->
  ex_Rbar_plus (LeftLim f x) (LeftLim g x) ->
  ex_left_lim (fun y => f y + g y) x.
Proof.
  move => /LeftLim_correct Hf /LeftLim_correct Hg Hl.
  exists (Rbar_plus (LeftLim f x) (LeftLim g x)).
  eapply is_left_lim_plus ; try eassumption.
  by apply Rbar_plus_correct.
Qed.
Lemma LeftLim_plus (f g : R -> R) (x : Rbar) :
  ex_left_lim f x -> ex_left_lim g x ->
  ex_Rbar_plus (LeftLim f x) (LeftLim g x) ->
  LeftLim (fun y => f y + g y) x = Rbar_plus (LeftLim f x) (LeftLim g x).
Proof.
  move => /LeftLim_correct Hf /LeftLim_correct Hg Hl.
  apply is_left_lim_unique.
  eapply is_left_lim_plus ; try eassumption.
  by apply Rbar_plus_correct.
Qed.

Lemma is_right_lim_plus (f g : R -> R) (x lf lg l : Rbar) :
  is_right_lim f x lf -> is_right_lim g x lg ->
  is_Rbar_plus lf lg l ->
  is_right_lim (fun y => f y + g y) x l.
Proof.
intros (?&Cf) (?&Cg) Hp.
split; auto.
eapply filterlim_comp_2 ; try eassumption.
by apply filterlim_Rbar_plus.
Qed.
Lemma is_right_lim_plus' (f g : R -> R) (x : Rbar) (lf lg : R) :
  is_right_lim f x lf -> is_right_lim g x lg ->
  is_right_lim (fun y => f y + g y) x (lf + lg).
Proof.
  intros Hf Hg.
  eapply is_right_lim_plus.
  by apply Hf.
  by apply Hg.
  by [].
Qed.
Lemma ex_right_lim_plus (f g : R -> R) (x : Rbar) :
  ex_right_lim f x -> ex_right_lim g x ->
  ex_Rbar_plus (RightLim f x) (RightLim g x) ->
  ex_right_lim (fun y => f y + g y) x.
Proof.
  move => /RightLim_correct Hf /RightLim_correct Hg Hl.
  exists (Rbar_plus (RightLim f x) (RightLim g x)).
  eapply is_right_lim_plus ; try eassumption.
  by apply Rbar_plus_correct.
Qed.
Lemma RightLim_plus (f g : R -> R) (x : Rbar) :
  ex_right_lim f x -> ex_right_lim g x ->
  ex_Rbar_plus (RightLim f x) (RightLim g x) ->
  RightLim (fun y => f y + g y) x = Rbar_plus (RightLim f x) (RightLim g x).
Proof.
  move => /RightLim_correct Hf /RightLim_correct Hg Hl.
  apply is_right_lim_unique.
  eapply is_right_lim_plus ; try eassumption.
  by apply Rbar_plus_correct.
Qed.

(** Left/Right limits of integral boundary *)

Lemma is_RInt_upper_bound_left_lim a b f v :
  Rlt a b ->
  is_RInt f a b v ->
  is_left_lim (RInt f a) b (RInt f a b).
Proof.
  intros Hlt His.
  unfold is_left_lim. split; first done.
  unfold filterlim, filter_le, filtermap, Rbar_at_left, within, Rbar_locally, locally. intros P HP.
  destruct HP as (eps&Heps).
  cut (∃ eps' : posreal, ∀ y, ball b eps' y -> Rbar_lt y b -> ball (RInt f a b) eps (RInt f a y)).
  { intros (eps'&Heps'). exists eps'. intros y Hball Hbar. apply Heps, Heps'; auto. }
  edestruct (ex_RInt_ub f a b) as (ub&Hub); first (econstructor; eauto).
  assert (∀ t, a <= t <= b -> Rabs (RInt f t b) <= (b - t) * ub).
  { intros t Hle. apply abs_RInt_le_const; intuition.
    { apply: ex_RInt_Chasles_2.
      { split; eassumption. }
      econstructor; eauto. }
    apply Hub. split.
    { rewrite Rmin_left; nra. }
    { rewrite Rmax_right; nra. }
  }
  assert (0 <= ub).
  { specialize (Hub a). transitivity (norm (f a)).
    { apply norm_ge_0. }
    { apply Hub. rewrite Rmin_left ?Rmax_right; nra. }
  }
  assert (Heps': 0 < eps / (ub + 1)).
  { apply Rdiv_lt_0_compat.
    { destruct eps; auto. }
    { nra. }
  }
  set (eps' := (mkposreal _ Heps')).
  edestruct (eps_squeeze_between a b eps') as (eps''&Hsmaller&Heps''); auto.
  exists eps''.
  rewrite /ball/=/AbsRing_ball/=/abs/=/minus/plus/opp/=.
  intros y Hball Hlty.
  assert (a <= y).
  { apply Heps''. auto. }
  rewrite -(RInt_Chasles f a y b); swap 1 3.
  { eapply ex_RInt_Chasles_2; last first.
    { econstructor; eauto. }
    split; nra. }
  { eapply ex_RInt_Chasles_1; last first.
    { econstructor; eauto. }
    split; nra. }
  eapply (Rle_lt_trans _ (Rabs (RInt f y b))).
  { right. rewrite -Rabs_Ropp. f_equal. rewrite /plus//=. nra. }
  eapply (Rle_lt_trans); first (eapply H; nra).
  rewrite Rabs_left in Hball; last first.
  { nra. }
  assert (b - y < eps'' ) by nra.
  apply (Rle_lt_trans _ (eps' * ub)).
  { apply Rmult_le_compat_r; nra. }
  rewrite /eps' /=. rewrite /Rdiv. rewrite Rmult_assoc.
  apply (Rlt_le_trans _ (eps * 1)); last nra.
  apply Rmult_lt_compat_l; first by (destruct eps).
  rewrite Rmult_comm. apply (Rdiv_lt_1 ub (ub + 1)); nra.
Qed.

Lemma is_RInt_lower_bound_right_lim a b f v :
  Rlt a b ->
  is_RInt f a b v ->
  is_right_lim (λ x, RInt f x b) a (RInt f a b).
Proof.
  intros Hlt His.
  unfold is_right_lim. split; first done.
  unfold filterlim, filter_le, filtermap, Rbar_at_right, within, Rbar_locally, locally. intros P HP.
  destruct HP as (eps&Heps).
  cut (∃ eps' : posreal, ∀ y, ball a eps' y -> Rbar_lt a y -> ball (RInt f a b) eps (RInt f y b)).
  { intros (eps'&Heps'). exists eps'. intros y Hball Hbar. apply Heps, Heps'; auto. }
  edestruct (ex_RInt_ub f a b) as (ub&Hub); first (econstructor; eauto).
  assert (∀ t, a <= t <= b -> Rabs (RInt f a t) <= (t - a) * ub).
  { intros t Hle. apply abs_RInt_le_const; intuition.
    { apply: ex_RInt_Chasles_1.
      { split; eassumption. }
      econstructor; eauto. }
    apply Hub. split.
    { rewrite Rmin_left; nra. }
    { rewrite Rmax_right; nra. }
  }
  assert (0 <= ub).
  { specialize (Hub a). transitivity (norm (f a)).
    { apply norm_ge_0. }
    { apply Hub. rewrite Rmin_left ?Rmax_right; nra. }
  }
  assert (Heps': 0 < eps / (ub + 1)).
  { apply Rdiv_lt_0_compat.
    { destruct eps; auto. }
    { nra. }
  }
  set (eps' := (mkposreal _ Heps')).
  edestruct (eps_squeeze_between' a b eps') as (eps''&Hsmaller&Heps''); auto.
  exists eps''.
  rewrite /ball/=/AbsRing_ball/=/abs/=/minus/plus/opp/=.
  intros y Hball Hlty.
  assert (y <= b).
  { apply Heps''. auto. }
  rewrite -(RInt_Chasles f a y b); swap 1 3.
  { eapply ex_RInt_Chasles_2; last first.
    { econstructor; eauto. }
    split; nra. }
  { eapply ex_RInt_Chasles_1; last first.
    { econstructor; eauto. }
    split; nra. }
  eapply (Rle_lt_trans _ (Rabs (RInt f a y))).
  { right. rewrite -Rabs_Ropp. f_equal. rewrite /plus//=. nra. }
  eapply (Rle_lt_trans); first (eapply H; nra).
  rewrite Rabs_right in Hball; last first.
  { nra. }
  assert (y - a < eps'' ) by nra.
  apply (Rle_lt_trans _ (eps' * ub)).
  { apply Rmult_le_compat_r; nra. }
  rewrite /eps' /=. rewrite /Rdiv. rewrite Rmult_assoc.
  apply (Rlt_le_trans _ (eps * 1)); last nra.
  apply Rmult_lt_compat_l; first by (destruct eps).
  rewrite Rmult_comm. apply (Rdiv_lt_1 ub (ub + 1)); nra.
Qed.
Lemma is_RInt_comp' : ∀ (f : R → R) (g dg : R → R) (a b : R),
    a <= b →
    (∀ x : R, a <= x <= b → continuous f (g x)) →
    (∀ x : R, a <= x <= b → is_derive g x (dg x) ∧ continuous dg x) →
    is_RInt (λ y : R, scal (dg y) (f (g y))) a b (RInt f (g a) (g b)).
Proof.
  intros f g dg a b Hle Hcont Hdiff. apply: is_RInt_comp.
  - intros x. rewrite Rmin_left // Rmax_right //. apply Hcont.
  - intros x. rewrite Rmin_left // Rmax_right //. apply Hdiff.
Qed.

Lemma RInt_comp' : ∀ (f : R → R) (g dg : R → R) (a b : R),
    a <= b →
    (∀ x : R, a <= x <= b → continuous f (g x)) →
    (∀ x : R, a <= x <= b → is_derive g x (dg x) ∧ continuous dg x) →
    RInt (λ y : R, scal (dg y) (f (g y))) a b = RInt f (g a) (g b).
Proof.
  intros f g dg a b Hle Hcont Hdiff. apply: RInt_comp.
  - intros x. rewrite Rmin_left // Rmax_right //. apply Hcont.
  - intros x. rewrite Rmin_left // Rmax_right //. apply Hdiff.
Qed.

Lemma Rbar_at_left_interval a b (P: Rbar -> Prop) :
  Rbar_lt a b ->
  (∀ x, Rbar_lt a x -> Rbar_lt x b -> P x) ->
  Rbar_at_left b P.
Proof.
  intros Hlt HP. unfold Rbar_at_left, within.
  apply open_Rbar_gt' in Hlt. move:Hlt. apply filter_imp.
  intros. apply HP; auto.
Qed.

Lemma Rbar_at_right_interval a b (P: Rbar -> Prop) :
  Rbar_lt a b ->
  (∀ x, Rbar_lt a x -> Rbar_lt x b -> P x) ->
  Rbar_at_right a P.
Proof.
  intros Hlt HP. unfold Rbar_at_right, within.
  apply open_Rbar_lt' in Hlt. move:Hlt. apply filter_imp.
  intros. apply HP; auto.
Qed.

Lemma ball_interval_lb r eps x :
  ball r eps x ->
  r - eps < x.
Proof.
  rewrite /ball/=/AbsRing_ball/abs/=/minus/plus/opp//=. apply Rabs_case; nra.
Qed.

Lemma ball_interval_ub r eps x :
  ball r eps x ->
  x < r + eps.
Proof.
  rewrite /ball/=/AbsRing_ball/abs/=/minus/plus/opp//=. apply Rabs_case; nra.
Qed.

Lemma not_Rbar_at_left b P :
  ¬ Rbar_at_left b P →
  match b with
  | Finite r => ∀ eps : posreal, ∃ x, r - eps < x < r ∧ ¬ P x
  | p_infty => ∀ M, ∃ x, M < x ∧ ¬ P x
  | m_infty => True
  end.
Proof.
  intros Hneg.
  destruct b; auto.
  - intros eps. unfold Rbar_at_left, within, Rbar_locally, locally in Hneg.
    specialize (Classical_Pred_Type.not_ex_all_not _ _ Hneg eps) => /= Heps.
    apply Classical_Pred_Type.not_all_ex_not in Heps.
    destruct Heps as (x&Hx).
    assert (Hx': ¬ ((ball r eps x ∧ x < r) → P x)) by intuition.
    eapply Classical_Prop.not_imply_elim in Hx'.
    exists x.
    split; last first.
    { eapply Classical_Prop.not_imply_elim2 in Hx; eauto. }
    intuition.
    apply ball_interval_lb; auto.
  - intros M. unfold Rbar_at_left, within, Rbar_locally, locally in Hneg.
    specialize (Classical_Pred_Type.not_ex_all_not _ _ Hneg M) => /= Heps.
    apply Classical_Pred_Type.not_all_ex_not in Heps.
    destruct Heps as (x&Hx).
    assert (Hx': ¬ (M < x → P x)) by intuition.
    eapply Classical_Prop.not_imply_elim in Hx'.
    exists x.
    split; last first.
    { eapply Classical_Prop.not_imply_elim2 in Hx; eauto. }
    auto.
Qed.

Lemma interval_inhabited (x y : R) : x < y -> ∃ z, x < z < y.
Proof.
  intros.
  edestruct (boule_of_interval x y) as (s&(r&Heq1&Heq2)); auto.
  exists s. nra.
Qed.

Lemma Rbar_at_left_witness (r: R) (eps: posreal) P:
  Rbar_at_left r P -> ∃ x, r - eps < x < r ∧ P x.
Proof.
  unfold Rbar_at_left, within, Rbar_locally, locally.
  intros Hex. destruct Hex as (eps'&Heps').
  set (lb := r - Rmin eps eps').
  edestruct (interval_inhabited lb r) as (x&Hin).
  { rewrite /lb. apply Rmin_case; destruct eps, eps' => /=; nra. }
  exists x. split.
  { move: Hin. rewrite /lb. apply Rmin_case_strong; destruct eps, eps' => /=; nra. }
  apply Heps'; last by intuition.
  rewrite /ball/=/AbsRing_ball/abs/=/minus/plus/opp//=.
  { move: Hin. rewrite /lb. apply Rabs_case; apply Rmin_case_strong; destruct eps, eps' => /=; nra. }
Qed.

Lemma Rbar_at_left_witness_above (r: R) y P:
  Rbar_at_left r P -> y < r -> ∃ x, y < x < r ∧ P x.
Proof.
  intros. assert (Hpos: 0 < r - y) by nra.
  edestruct (Rbar_at_left_witness r (mkposreal _ Hpos) P) as (x&?&HP); auto.
  exists x. split; auto.
  simpl in H1. nra.
Qed.

Lemma Rbar_at_left_witness_above_p_infty y P:
  Rbar_at_left p_infty P -> ∃ x, y < x ∧ P x.
Proof.
  unfold Rbar_at_left, within, Rbar_locally.
  intros HM. destruct HM as (M&HM). exists (Rmax (M + 1) (y + 1)).
  split.
  - apply (Rlt_le_trans _ (y + 1)); first nra.
    apply Rmax_r.
  - apply HM; simpl; auto.
  - apply (Rlt_le_trans _ (M + 1)); first nra.
    apply Rmax_l.
Qed.
