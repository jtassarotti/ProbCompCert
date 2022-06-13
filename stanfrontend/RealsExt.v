Require Export RelationClasses Morphisms Utf8.
From mathcomp Require Import ssreflect ssrbool eqtype.
From Coquelicot Require Import Hierarchy Markov Rcomplements Rbar Lub Lim_seq SF_seq Continuity Hierarchy RInt RInt_analysis Derive.

Require ClassicalEpsilon.
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

 Lemma piecewise_continuity b h f1 f2 :
   (∀ x, x <= b -> h x = f1 x) ->
   (∀ x, b <= x -> h x = f2 x) ->
   continuity f1 ->
   continuity f2 ->
   continuity h.
Proof.
  intros Hf1 Hf2 Hcf1 Hcf2.
  unfold continuity. intros x.
  destruct (Rlt_dec x b).
  { eapply continuity_pt_ext_loc; last eapply Hcf1.
    apply (locally_interval _ x m_infty b); simpl; auto. intros. symmetry; eapply Hf1; nra.
  }
  destruct (Rlt_dec b x).
  { eapply continuity_pt_ext_loc; last eapply Hcf2.
    apply (locally_interval _ x b p_infty); simpl; auto. intros. symmetry; eapply Hf2; nra.
  }
  assert (x = b) as <- by nra; subst.
  move: Hcf1 Hcf2.
  unfold continuity, continuity_pt, continue_in, limit1_in, limit_in, D_x, no_cond.
  intros Hcf1 Hcf2 eps Hpos.
  destruct (Hcf1 x eps Hpos) as (alp1&Halp1pos&Halp1).
  destruct (Hcf2 x eps Hpos) as (alp2&Halp2pos&Halp2).
  exists (Rmin alp1 alp2).
  split.
  { apply Rlt_gt. apply Rmin_case; nra. }
  simpl.
  intros x' (Hneq&Hdist).
  destruct (Rlt_dec x' x).
  { rewrite ?Hf1; try nra. apply Halp1. split; first auto.
    move: Hdist. simpl. apply Rmin_case_strong; nra. }
  destruct (Rlt_dec x x').
  { rewrite ?Hf2; try nra. apply Halp2. split; first auto.
    move: Hdist. simpl. apply Rmin_case_strong; nra. }
  nra.
Qed.

Lemma continuous_continuity_pt f x :
  continuous f x <-> continuity_pt f x.
Proof. rewrite /continuous continuity_pt_filterlim //. Qed.


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

Lemma ex_RInt_comp' : ∀ (f : R → R) (g dg : R → R) (a b : R),
    a <= b →
    (∀ x : R, a <= x <= b → continuous f (g x)) →
    (∀ x : R, a <= x <= b → is_derive g x (dg x) ∧ continuous dg x) →
    ex_RInt (λ y : R, scal (dg y) (f (g y))) a b.
Proof.
  intros f g dg a b Hle Hcont Hdiff. eexists; apply: is_RInt_comp'; auto.
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

Lemma not_Rbar_at_right b P :
  ¬ Rbar_at_right b P →
  match b with
  | Finite r => ∀ eps : posreal, ∃ x, r < x < r + eps ∧ ¬ P x
  | p_infty => True
  | m_infty =>  ∀ M, ∃ x, x < M ∧ ¬ P x
  end.
Proof.
  intros Hneg.
  destruct b; auto.
  - intros eps. unfold Rbar_at_right, within, Rbar_locally, locally in Hneg.
    specialize (Classical_Pred_Type.not_ex_all_not _ _ Hneg eps) => /= Heps.
    apply Classical_Pred_Type.not_all_ex_not in Heps.
    destruct Heps as (x&Hx).
    assert (Hx': ¬ ((ball r eps x ∧ r < x) → P x)) by intuition.
    eapply Classical_Prop.not_imply_elim in Hx'.
    exists x.
    split; last first.
    { eapply Classical_Prop.not_imply_elim2 in Hx; eauto. }
    intuition.
    apply ball_interval_ub; auto.
  - intros M. unfold Rbar_at_right, within, Rbar_locally, locally in Hneg.
    specialize (Classical_Pred_Type.not_ex_all_not _ _ Hneg M) => /= Heps.
    apply Classical_Pred_Type.not_all_ex_not in Heps.
    destruct Heps as (x&Hx).
    assert (Hx': ¬ (x < M → P x)) by intuition.
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

Lemma Rbar_at_left_strict_monotone (t : R) (b : Rbar) g glim :
  Rbar_lt t b →
  (∀ x y, t <= x < y → Rbar_lt y b → g x < g y) →
  is_left_lim g b glim ->
  Rbar_at_left b (λ y : Rbar, Rbar_lt (g y) glim).
Proof.
  unfold is_left_lim.
  intros Hltb Ht (Hnm&Hlim).
  apply Classical_Prop.NNPP. intros Hneg%not_Rbar_at_left.
  destruct b; try congruence.
  - unfold filterlim, filter_le, filtermap in Hlim.
    assert (Hpos: 0 < r - t).
    { simpl in Hltb. nra. }
    set (eps' := mkposreal _ Hpos).
    specialize (Hneg eps').
    assert (∃ x : R, (r - eps' < x ∧ x < r) ∧ Rbar_lt glim (g x)) as (x&Hrange&r0).
    {
      destruct Hneg as (x&Hrange&Hnlt).
      apply Rbar_not_lt_le in Hnlt.
      apply Rbar_le_lt_or_eq_dec in Hnlt.
      destruct Hnlt as [Hlt|Heq].
      { exists x. split; eauto. }
      destruct (interval_inhabited x r) as (x'&Hx'1&Hx'2); first nra.
      exists x'.
      split; first nra.
      rewrite Heq. simpl. apply Ht; auto; split; try nra.
      move: Hrange. rewrite /eps' /=. nra.
    }
    apply open_Rbar_lt' in r0. apply Hlim in r0.
    eapply (Rbar_at_left_witness_above r x) in r0; try (intuition eauto; done).
    destruct r0 as (y&Hrange'&Hlt).
    simpl in Hlt. apply Rlt_not_le in Hlt.
    apply Hlt. left. apply Ht; simpl; simpl in Hltb; try nra.
    split; last by intuition.
    move: Hrange. rewrite /eps' /=. nra.
  - unfold filterlim, filter_le, filtermap in Hlim.
    specialize (Hneg t).
    assert (∃ x : R, t < x ∧ Rbar_lt glim (g x)) as (x&Hrange&r0).
    {
      destruct Hneg as (x&Hrange&Hnlt).
      apply Rbar_not_lt_le in Hnlt.
      apply Rbar_le_lt_or_eq_dec in Hnlt.
      destruct Hnlt as [Hlt|Heq].
      { exists x. split; eauto. }
      exists (x + 1).
      split; first nra.
      rewrite Heq. simpl. apply Ht; auto; split; try nra.
    }
    apply open_Rbar_lt' in r0. apply Hlim in r0.
    eapply (Rbar_at_left_witness_above_p_infty x) in r0; try (intuition eauto; done).
    destruct r0 as (y&Hrange'&Hlt).
    simpl in Hlt. apply Rlt_not_le in Hlt.
    apply Hlt. left. apply Ht; simpl; simpl in Hltb; try nra.
Qed.

Lemma Rbar_at_right_witness (r: R) (eps: posreal) P:
  Rbar_at_right r P -> ∃ x, r < x < r + eps ∧ P x.
Proof.
  unfold Rbar_at_right, within, Rbar_locally, locally.
  intros Hex. destruct Hex as (eps'&Heps').
  set (lb := r + Rmin eps eps').
  edestruct (interval_inhabited r lb) as (x&Hin).
  { rewrite /lb. apply Rmin_case; destruct eps, eps' => /=; nra. }
  exists x. split.
  { move: Hin. rewrite /lb. apply Rmin_case_strong; destruct eps, eps' => /=; nra. }
  apply Heps'; last by intuition.
  rewrite /ball/=/AbsRing_ball/abs/=/minus/plus/opp//=.
  { move: Hin. rewrite /lb. apply Rabs_case; apply Rmin_case_strong; destruct eps, eps' => /=; nra. }
Qed.

Lemma Rbar_at_right_witness_above (r: R) y P:
  Rbar_at_right r P -> r < y -> ∃ x, r < x < y ∧ P x.
Proof.
  intros. assert (Hpos: 0 < y - r) by nra.
  edestruct (Rbar_at_right_witness r (mkposreal _ Hpos) P) as (x&?&HP); auto.
  exists x. split; auto.
  simpl in H1. nra.
Qed.

Lemma Rbar_at_right_witness_above_m_infty y P:
  Rbar_at_right m_infty P -> ∃ x, x < y ∧ P x.
Proof.
  unfold Rbar_at_right, within, Rbar_locally.
  intros HM. destruct HM as (M&HM). exists (Rmin (M - 1) (y - 1)).
  split.
  - apply (Rle_lt_trans _ (y - 1)); last nra.
    apply Rmin_r.
  - apply HM; simpl; auto.
  - apply (Rle_lt_trans _ (M - 1)); last nra.
    apply Rmin_l.
Qed.

Lemma Rbar_at_right_strict_monotone (t : R) (a : Rbar) g glim :
  Rbar_lt a t →
  (∀ x y, x < y <= t → Rbar_lt a x → g x < g y) →
  is_right_lim g a glim ->
  Rbar_at_right a (λ y : Rbar, Rbar_lt glim (g y)).
Proof.
  unfold is_left_lim.
  intros Hltb Ht (Hnm&Hlim).
  apply Classical_Prop.NNPP. intros Hneg%not_Rbar_at_right.
  destruct a; try congruence.
  - unfold filterlim, filter_le, filtermap in Hlim.
    assert (Hpos: 0 < t - r).
    { simpl in Hltb. nra. }
    set (eps' := mkposreal _ Hpos).
    specialize (Hneg eps').
    assert (∃ x : R, (r < x ∧ x < r + eps') ∧ Rbar_lt (g x) glim) as (x&Hrange&r0).
    {
      destruct Hneg as (x&Hrange&Hnlt).
      apply Rbar_not_lt_le in Hnlt.
      apply Rbar_le_lt_or_eq_dec in Hnlt.
      destruct Hnlt as [Hlt|Heq].
      { exists x. split; eauto. }
      destruct (interval_inhabited r x) as (x'&Hx'1&Hx'2); first nra.
      exists x'.
      split; first nra.
      rewrite -Heq. simpl. apply Ht; auto; simpl; try nra. split; try nra.
      move: Hrange. rewrite /eps' /=. nra.
    }
    apply open_Rbar_gt' in r0. apply Hlim in r0.
    eapply (Rbar_at_right_witness_above r x) in r0; try (intuition eauto; done).
    destruct r0 as (y&Hrange'&Hlt).
    simpl in Hlt. apply Rlt_not_le in Hlt.
    apply Hlt. left. apply Ht; simpl; simpl in Hltb; try nra.
    split; first by intuition.
    move: Hrange. rewrite /eps' /=. nra.
  - unfold filterlim, filter_le, filtermap in Hlim.
    specialize (Hneg t).
    assert (∃ x : R, x < t ∧ Rbar_lt (g x) glim) as (x&Hrange&r0).
    {
      destruct Hneg as (x&Hrange&Hnlt).
      apply Rbar_not_lt_le in Hnlt.
      apply Rbar_le_lt_or_eq_dec in Hnlt.
      destruct Hnlt as [Hlt|Heq].
      { exists x. split; eauto. }
      exists (x - 1).
      split; first nra.
      rewrite -Heq. simpl. apply Ht; auto; split; try nra.
    }
    apply open_Rbar_gt' in r0. apply Hlim in r0.
    eapply (Rbar_at_right_witness_above_m_infty x) in r0; try (intuition eauto; done).
    destruct r0 as (y&Hrange'&Hlt).
    simpl in Hlt. apply Rlt_not_le in Hlt.
    apply Hlt. left. apply Ht; simpl; simpl in Hltb; try nra.
Qed.

Lemma is_lim_right_lim f x v :
  x <> p_infty ->
  is_lim f x v -> is_right_lim f x v.
Proof.
  rewrite /is_lim/is_right_lim. intros ? Hfilt; split; auto.
  move: Hfilt.
  apply filterlim_filter_le_1.
  unfold filter_le. intros P.
  unfold Rbar_at_right, within, Rbar_locally, Rbar_locally'.
  destruct x.
  { unfold locally', within. apply filter_imp. simpl. intros ? Himp ?. apply Himp; nra. }
  { congruence. }
  {intros (M&HM). exists M. intros. apply HM. auto. }
Qed.


Lemma is_lim_left_lim f x v :
  x <> m_infty ->
  is_lim f x v -> is_left_lim f x v.
Proof.
  rewrite /is_lim/is_left_lim. intros ? Hfilt; split; auto.
  move: Hfilt.
  apply filterlim_filter_le_1.
  unfold filter_le. intros P.
  unfold Rbar_at_left, within, Rbar_locally, Rbar_locally'.
  destruct x.
  { unfold locally', within. apply filter_imp. simpl. intros ? Himp ?. apply Himp; nra. }
  {intros (M&HM). exists M. intros. apply HM. auto. }
  { congruence. }
Qed.

Section comp.

  Lemma R_dist_plus_r1 x y z y':
    R_dist x (y + z) <= R_dist x (y' + z) + R_dist y y'.
  Proof.
    rewrite /R_dist.
    replace (y + z) with (y' + z + (y - y')) by nra.
    replace (x - (y' + z + (y - y'))) with ((x - (y' + z)) - (y - y')) by nra.
    rewrite -(Rabs_Ropp (y - y')).
    etransitivity; last eapply Rabs_triang.
    reflexivity.
  Qed.

  Lemma ex_RInt_bounding (f: R -> R) (a b : R) eps :
    a <= b ->
    ex_RInt f a b ->
    ∃ g1 g2, (∀ x, a <= x <= b -> g1 x <= f x <= g2 x) /\
             (∀ x, a <= x <= b -> continuous g1 x) /\
             (∀ x, a <= x <= b -> continuous g2 x) /\
             (RInt (λ x, g2 x - g1 x) a b < eps).
  Proof.
    admit.
  Admitted.

Require Import Program.Basics.
Instance Rle_trans_proper_left: Proper (Rle ==> eq ==> flip impl) Rle.
Proof. intros ?? Hle ?? Hle'. rewrite /flip/impl/=. nra. Qed.
Instance Rle_trans_proper_right: Proper (eq ==> Rle ==> impl) Rle.
Proof. intros ?? Hle ?? Hle'. rewrite /flip/impl/=. nra. Qed.
Instance Rlt_trans_proper_left: Proper (Rlt ==> eq ==> flip impl) Rlt.
Proof. intros ?? Hle ?? Hle'. rewrite /flip/impl/=. nra. Qed.
Instance Rlt_trans_proper_right: Proper (eq ==> Rlt ==> impl) Rlt.
Proof. intros ?? Hle ?? Hle'. rewrite /flip/impl/=. nra. Qed.
Instance Rlt_Rle_trans_proper_left: Proper (Rle ==> eq ==> flip impl) Rlt.
Proof. intros ?? Hle ?? Hle'. rewrite /flip/impl/=. nra. Qed.
Instance Rlt_Rle_trans_proper_right: Proper (eq ==> Rle ==> impl) Rlt.
Proof. intros ?? Hle ?? Hle'. rewrite /flip/impl/=. nra. Qed.

Lemma RiemannInt_SF_proof_irrel a b f (Hpf1 Hpf2 : IsStepFun _ a b) :
  RiemannInt_SF  {| fe := f; pre := Hpf1 |} =
  RiemannInt_SF  {| fe := f; pre := Hpf2 |}.
Proof.
  destruct (Rle_dec a b).
  { apply Rle_antisym; apply StepFun_P37; eauto; intros => //=; nra. }
  rewrite StepFun_P39.
  symmetry. rewrite StepFun_P39.
  f_equal.
  { apply Rle_antisym; apply StepFun_P37; eauto; intros => //=; nra. }
Qed.

Lemma StepFun_P30':
  ∀ (a b l : R) (f g : StepFun a b) (Hpf : IsStepFun _ a b),
    RiemannInt_SF {| fe := λ x : R, f x + l * g x; pre := Hpf |} =
    RiemannInt_SF f + l * RiemannInt_SF g.
Proof.
  intros. rewrite -StepFun_P30.
  apply RiemannInt_SF_proof_irrel.
Qed.

Lemma RiemannInt_SF_ext :
  ∀ (a b : R) (f g : StepFun a b), (∀ x : R, Rmin a b <= x <= Rmax a b -> f x = g x) →
                                   RiemannInt_SF f = RiemannInt_SF g.
Proof.
  intros a b f g Heq.
  destruct (Rle_dec a b).
  { apply Rle_antisym; apply StepFun_P37; eauto; intros => //=; rewrite ?Heq; try nra;
    rewrite ?Rmin_left // ?Rmax_right //; nra. }
  rewrite StepFun_P39.
  symmetry. rewrite StepFun_P39.
  f_equal.
  { apply Rle_antisym; apply StepFun_P37; eauto; intros => //=; rewrite ?Heq; try nra;
    rewrite ?Rmax_left // ?Rmin_right //; nra. }
Qed.

Lemma RiemannInt_SF_ext' :
  ∀ (a b : R) (a' b': R) (f : StepFun a b) (g : StepFun a' b'),
    a = a' -> b = b' -> (∀ x : R, Rmin a b <= x <= Rmax a b -> f x = g x) → RiemannInt_SF f = RiemannInt_SF g.
Proof.
  intros a b a' b' f g ?? Heq.
  subst. eapply RiemannInt_SF_ext; eauto.
Qed.

Lemma Riemann_integrable_SF_aux a b sf (eps: posreal) :
  (∀ t : R, Rmin a b <= t <= Rmax a b → Rabs (sf t - sf t) <= {| fe := fct_cte 0; pre := StepFun_P4 a b 0 |} t)
  ∧ Rabs (RiemannInt_SF {| fe := fct_cte 0; pre := StepFun_P4 a b 0 |}) < eps.
Proof.
  split.
  - intros; replace (sf t - sf t) with 0 by nra; rewrite Rabs_right => //=; last nra; rewrite /fct_cte; nra.
  - simpl. rewrite StepFun_P18 Rabs_right => //=; destruct eps => /=; nra.
Qed.

Lemma Riemann_integrable_SF a b (sf: StepFun a b) :
  Riemann_integrable sf a b.
Proof.
  rewrite /Riemann_integrable => eps.
  exists sf.
  exists (mkStepFun (StepFun_P4 a b 0)).
  apply Riemann_integrable_SF_aux.
Defined.

Lemma seq2Rlist_id l : seq2Rlist l = l.
Proof. induction l => //=; congruence. Qed.

Lemma size_compat: ∀ s : list R, Datatypes.length s = seq.size s.
Proof. intros. rewrite -size_compat. rewrite seq2Rlist_id //. Qed.

Lemma R_dist_lt_all_eps' v1 v2 :
  (∀ (eps: posreal), R_dist v1 v2 < eps) -> ~ v1 < v2.
Proof.
  intros Hlt_eps Hlt.
  assert (Hpos: 0 < v2 - v1) by nra.
  specialize (Hlt_eps (mkposreal _ Hpos)).
  rewrite R_dist_sym in Hlt_eps.
  rewrite /R_dist Rabs_right //= in Hlt_eps; nra.
Qed.

Lemma R_dist_lt_all_eps v1 v2 :
  (∀ (eps: posreal), R_dist v1 v2 < eps) -> v1 = v2.
Proof.
  intros Hlt.
  destruct (Rle_dec v1 v2) as [[|]|n]; auto.
  { exfalso; eapply R_dist_lt_all_eps'; eauto. }
  apply Rnot_le_lt in n.
  { exfalso; eapply R_dist_lt_all_eps'; last eauto. intros. rewrite R_dist_sym; eauto. }
Qed.

Lemma RiemannInt_SF_RiemannInt a b (sf: StepFun a b) :
  RiemannInt (Riemann_integrable_SF a b sf) = RiemannInt_SF sf.
Proof.
  rewrite /RiemannInt//=.
  destruct (RiemannInt_exists _ _ _) as (v&Hv).
  rewrite /Un_cv//= in Hv.
  rewrite /phi_sequence/Riemann_integrable_SF/= in Hv.
  symmetry.
  apply R_dist_lt_all_eps. intros. edestruct (Hv eps) as (n&Hlt).
  { destruct eps; eauto. }
  apply (Hlt n); lia.
Qed.

Lemma is_RInt_of_SF a b (sf: StepFun a b) :
  a <= b ->
  is_RInt sf a b (RiemannInt_SF sf).
Proof. rewrite -RiemannInt_SF_RiemannInt. intros. apply: ex_RInt_Reals_aux_1. Qed.

Lemma ex_RInt_of_SF a b (sf: StepFun a b) :
  a <= b ->
  ex_RInt sf a b.
Proof. intros; eexists; eapply is_RInt_of_SF; auto. Qed.

Lemma RInt_of_SF a b (sf: StepFun a b) :
  a <= b ->
  RInt sf a b = RiemannInt_SF sf.
Proof. intros. by apply is_RInt_unique, is_RInt_of_SF. Qed.

Lemma is_pos_div_4: ∀ eps : posreal, 0 < eps / 4.
Proof.
  intros. specialize (is_pos_div_2 (mkposreal (eps /2) (is_pos_div_2 _))) => //=.
  nra.
Qed.

Lemma posreal_div_2_lt (eps: posreal) :
  eps / 2 < eps.
Proof.
  cut (eps < eps + eps).
  { nra. }
  destruct eps => //=. nra.
Qed.


  Lemma bounding_ex_RInt (f : R -> R) (a b : R) :
    a <= b ->
    (∀ eps, ∃ g1 g2, (∀ x, a <= x <= b -> g1 x <= f x <= g2 x) /\
             (∀ x, a <= x <= b -> continuous g1 x) /\
             (∀ x, a <= x <= b -> continuous g2 x) /\
             (RInt (λ x, g2 x - g1 x) a b < eps)) ->
    ex_RInt f a b.
  Proof.
    intros Hle Heps.
    apply ex_RInt_Reals_1.
    unfold Riemann_integrable. intros eps.
    set (eps' := mkposreal (eps/4) (is_pos_div_4 _)).
    set (eps'' := mkposreal (eps'/2) (is_pos_div_2 _)).
    specialize (Heps eps'').
    apply ClassicalEpsilon.constructive_indefinite_description in Heps as (g1&Heps).
    apply ClassicalEpsilon.constructive_indefinite_description in Heps as (g2&Heps).
    destruct Heps as (Hsandwich&Hg1cont&Hg2cont&Hdiff).
    assert (Hexg1: ex_RInt g1 a b).
    { apply: ex_RInt_continuous; rewrite Rmin_left // Rmax_right //. }
    assert (Hexg2: ex_RInt g2 a b).
    { apply: ex_RInt_continuous; rewrite Rmin_left // Rmax_right //. }
    assert (Hexdiff: ex_RInt (λ x, g2 x - g1 x) a b).
    { apply: ex_RInt_minus; eauto. }
    apply ex_RInt_Reals_0 in Hexg1.
    apply ex_RInt_Reals_0 in Hexg2.
    apply ex_RInt_Reals_0 in Hexdiff.
    destruct (Hexg1 eps') as (phi1&psi1&Hex1).
    destruct (Hexg2 eps') as (phi2&psi2&Hex2).
    destruct (Hexdiff eps'') as (phid&psid&Hexd).
    set (phi := λ x, phi1 x + 1 * phid x).
    assert (Hisphi: IsStepFun phi a b).
    { apply StepFun_P28. }
    set (psi_a := λ x, (mkStepFun (StepFun_P32 phid) x) + 1 * psi1 x).
    assert (Hispsi_a: IsStepFun psi_a a b).
    { apply StepFun_P28. }
    set (psi := λ x, mkStepFun Hispsi_a x + 2 * psid x).
    assert (Hispsi: IsStepFun psi a b).
    { apply StepFun_P28. }
    exists (mkStepFun Hisphi).
    exists (mkStepFun Hispsi).
    split.
    {
      intros t Hrange.
      rewrite /psi/=/psi_a/=.
      setoid_rewrite (R_dist_tri _ _ (g2 t)).
      rewrite /phi/=.
      setoid_rewrite (R_dist_plus_r1 (g2 t) _ _ (g1 t)).
      rewrite Rmult_1_l. rewrite {2}/R_dist.
      replace (g2 t - (g1 t + phid t)) with (g2 t - g1 t - phid t) by nra.
      destruct Hexd as (Hexd1&Hexd2).
      setoid_rewrite (Hexd1); auto.
      destruct Hex1 as (Hex11&Hex12).
      rewrite (R_dist_sym (phi1 t)).
      rewrite {2}/R_dist.
      setoid_rewrite Hex11; auto.
      assert (R_dist (f t) (g2 t) <= R_dist (g2 t) (g1 t)) as ->.
      { rewrite R_dist_sym. rewrite /R_dist. rewrite Rmin_left // Rmax_right // in Hrange.
        specialize (Hsandwich _ Hrange).
        rewrite ?Rabs_right; nra. }
      assert (R_dist (g2 t) (g1 t) <= Rabs (phid t) + psid t) as ->.
      { specialize (Hexd1 _ Hrange).
        rewrite /R_dist.
        cut (Rabs (g2 t - g1 t) - Rabs (phid t) <= psid t); first by nra.
        setoid_rewrite Rabs_triang_inv. auto.
      }
      nra.
    }
    rewrite /psi.
    rewrite (StepFun_P30').
    rewrite /psi_a.
    rewrite (StepFun_P30').
    setoid_rewrite Rabs_triang.
    setoid_rewrite Rabs_triang.
    rewrite ?Rabs_mult.
    destruct (Hex1) as (_&Hr1).
    destruct (Hex2) as (_&Hr2).
    destruct (Hexd) as (_&Hrd).
    replace (Rabs 1) with 1 by (rewrite Rabs_right; nra).
    rewrite Rmult_1_l.
    replace (Rabs 2) with 2 by (rewrite Rabs_right; nra).
    rewrite /eps'.
    cut (Rabs (RiemannInt_SF {| fe := λ x : R, Rabs (phid x); pre := StepFun_P32 phid |}) < eps').
    { move: Hr1 Hr2 Hrd.
      specialize (posreal_div_2_lt eps').
      { rewrite /eps'//=. intros. nra. }
    }
    rewrite -RInt_of_SF //=.
    assert (Hbound: ∀ x, a <= x <= b -> Rabs (phid x) <= Rabs (g2 x - g1 x - phid x) + (Rabs (g2 x - g1 x))).
    {
      intros x Hrange. rewrite -(Rabs_Ropp (g2 x - g1 x - phid x)).
      setoid_rewrite <-Rabs_triang. right. f_equal. nra.
    }
    assert (ex_RInt (λ x : R, Rabs (phid x)) a b).
    { apply ex_RInt_norm, ex_RInt_of_SF; auto. }
    rewrite Rabs_right; last first.
    { apply Rle_ge.
      apply RInt_ge_0; eauto.
      intros. apply Rabs_pos. }
    assert (ex_RInt (λ x : R, Rabs (g2 x - g1 x)) a b).
    { apply ex_RInt_norm; repeat apply: ex_RInt_minus;
      auto using ex_RInt_Reals_1, ex_RInt_of_SF. }
    assert (ex_RInt (λ y : R, Rabs (g2 y - g1 y - phid y)) a b).
    { apply ex_RInt_norm; repeat apply: ex_RInt_minus;
      auto using ex_RInt_Reals_1, ex_RInt_of_SF. }


    eapply Rle_lt_trans.
    { eapply RInt_le; auto; last first.
      { intros. eapply Hbound; nra. }
      { apply: ex_RInt_plus; auto. }
    }
    rewrite RInt_plus; auto.
    simpl.
    replace (eps /4) with (eps/4/2 + eps/4/2) by nra.
    apply Rplus_lt_compat.
    * eapply Rle_lt_trans.
      { apply (RInt_le _ psid); eauto.
        { apply ex_RInt_of_SF; eauto. }
        intros. apply Hexd. rewrite Rmin_left // Rmax_right //. nra.
      }
      eapply Rle_lt_trans; first eapply Rle_abs.
      rewrite RInt_of_SF //.
    * erewrite RInt_ext; first eauto.
      intros x. rewrite Rmin_left // Rmax_right // => ?. rewrite Rabs_right //.
      specialize (Hsandwich x). nra.
  Qed.

Lemma Rmin_diff_eq x y:
  Rmin x y = (x + y) / 2 - Rabs(x - y) / 2.
Proof.
  apply Rmin_case_strong; apply Rabs_case; nra.
Qed.

Lemma Rmax_diff_eq x y:
  Rmax x y = (x + y) / 2 + Rabs(x - y) / 2.
Proof.
  apply Rmax_case_strong; apply Rabs_case; nra.
Qed.

  Lemma bounding_ex_RInt' (f : R -> R) (a b : R) :
    a <= b ->
    (∀ eps, ∃ g1 g2, (∀ x, a <= x <= b -> (g1 x <= f x <= g2 x) ∨ (g2 x <= f x <= g1 x)) /\
             (∀ x, a <= x <= b -> continuous g1 x) /\
             (∀ x, a <= x <= b -> continuous g2 x) /\
             (RInt (λ x, Rabs (g2 x - g1 x)) a b < eps)) ->
    ex_RInt f a b.
  Proof.
    intros Hle Heps.
    eapply bounding_ex_RInt; eauto.
    intros eps.
    edestruct (Heps eps) as (g1&g2&Hrange&Hcont1&Hcont2&Hint).
    set (g1' := λ x, Rmin (g1 x) (g2 x)).
    set (g2' := λ x, Rmax (g1 x) (g2 x)).
    exists g1', g2'.
    split; [| split; [| split]].
    * intros x Hrange'. specialize (Hrange x Hrange').
      rewrite /g1'/g2'. destruct Hrange; apply Rmin_case_strong; apply Rmax_case_strong; nra.
    * intros. rewrite /g1'. eapply continuous_ext.
      { intros. symmetry. eapply Rmin_diff_eq. }
      { apply: continuous_minus. apply: continuous_scal.
        apply: continuous_plus; auto.
        apply: continuous_const.
        apply: continuous_scal; try apply continuous_const.
        apply continuous_comp.
        { apply: continuous_minus; auto. }
        { eapply continuous_continuity_pt.
          apply Rcontinuity_abs. }
      }
    * intros. rewrite /g2'. eapply continuous_ext.
      { intros. symmetry. eapply Rmax_diff_eq. }
      { apply: continuous_plus. apply: continuous_scal.
        apply: continuous_plus; auto.
        apply: continuous_const.
        apply: continuous_scal; try apply continuous_const.
        apply continuous_comp.
        { apply: continuous_minus; auto. }
        { eapply continuous_continuity_pt.
          apply Rcontinuity_abs. }
      }
    * eapply Rle_lt_trans; last eassumption.
      right. eapply RInt_ext.
      intros. rewrite /g2'/g1'.
      apply Rmax_case_strong; apply Rmin_case_strong; apply Rabs_case; try nra.
  Qed.

Definition logit u := ln (u / (1 - u)).
Definition logit_inv u := 1 / (1 + exp(-u)).
Definition unconstrain_lb_ub a b x :=
  logit ((x - a) / (b - a)).
Definition constrain_lb_ub a b x :=
  a + (b - a) * logit_inv x.
Definition deriv_constrain_lb_ub a b x :=
  (b - a) * logit_inv x * (1 - logit_inv x).


Require Import Coquelicot.AutoDerive.

Lemma deriv_constrain_lb_ub_correct a b x:
  is_derive (constrain_lb_ub a b) x (deriv_constrain_lb_ub a b x).
Proof.
  rewrite /constrain_lb_ub/deriv_constrain_lb_ub/logit_inv.
  assert (1 + exp (- x) ≠ 0).
  { specialize (exp_pos (- x)). nra. }
  auto_derive; auto. field; auto.
Qed.

Lemma logit_inv_range x :
   0 < logit_inv x < 1.
Proof.
  rewrite /logit_inv; specialize (exp_pos (-x)); intros; split.
  - apply Rdiv_lt_0_compat; nra.
  - apply Rlt_div_l; nra.
Qed.

Lemma deriv_constrain_lb_ub_pos a b x:
  a < b ->
  0 < deriv_constrain_lb_ub a b x.
Proof.
  rewrite /deriv_constrain_lb_ub.
  specialize (logit_inv_range x) => ??.
  apply Rmult_lt_0_compat; last by nra.
  apply Rmult_lt_0_compat; nra.
Qed.

Lemma constrain_lb_ub_increasing a b :
  a <= b ->
  increasing (constrain_lb_ub a b).
Proof.
  rewrite /constrain_lb_ub.
  intros Hrange x y Hle. rewrite /logit_inv.
  apply Rplus_le_compat_l.
  apply Rmult_le_compat_l; first nra.
  apply Rmult_le_compat_l; first nra.
  apply Rinv_le_contravar.
  { specialize (exp_pos (- y)). nra. }
  apply Rplus_le_compat_l.
  destruct Hle; last by (subst; nra).
  left.
  apply exp_increasing; nra.
Qed.

Lemma logit_inv_spec x :
  0 < x < 1 -> logit_inv (logit x) = x.
Proof.
  intros.
  rewrite /logit_inv/logit. rewrite exp_Ropp. rewrite exp_ln.
  { field; nra. }
  { apply Rdiv_lt_0_compat; nra. }
Qed.

Lemma constrain_lb_ub_inv :
  forall a b x, a < x < b -> constrain_lb_ub a b (unconstrain_lb_ub a b x) = x.
Proof.
  intros a b x Hrange. rewrite /constrain_lb_ub/unconstrain_lb_ub.
  rewrite logit_inv_spec.
  { field. nra. }
  split.
  { apply Rdiv_lt_0_compat; nra. }
  { apply Rlt_div_l; nra. }
Qed.

Lemma constrain_lb_ub_spec a b x :
  a <= b ->
  a <= constrain_lb_ub a b x <= b.
Proof.
  rewrite /constrain_lb_ub. specialize (logit_inv_range x); nra.
Qed.

(* A Darboux function has the IVT property: *)
(*
Definition is_Darboux a b f :=
  (∀ x y v, a <= Rmin x y /\ Rmax x y <= b -> f(x) <= v <= f(y) -> ∃ z, Rmin x y <= z <= Rmax x y /\ f(z) = v).

Lemma is_derive_Darboux a b f df:
  (∀ x, a <= x <= b -> is_derive f x (df x)) ->
  is_Darboux a b df.
Proof.
  set (f' := extension_C1 f df a b).
  set (df' := extension_C0 df a b).
  intros Hderiv.
  intros x y v Hrange Hv.
  set (c := (Rmin x y + Rmax x y)/2).
  set (alpha :=
         λ t, match Rle_dec t c with
              | left _ => Rmin x y
              | right _ => 2 * t - Rmax x y
              end).
  set (beta :=
         λ t, match Rle_dec t c with
              | left _ => Rmax x y
              | right _ => 2 * t - Rmin x y
              end).
  set (g := λ t, (f' (beta t) - f' (alpha t)) / (beta t - alpha t)).
  destruct (Req_dec (Rmin x y) (Rmax x y)) as [Heq|Hneq].
  {
    specialize (Rmin_Rmax_r x y).
    specialize (Rmin_Rmax_l x y).
    intros. assert (x = y) by nra. subst. exists y. nra.
  }
  exists (Rmin x y).  subst. idtac. subst.
  assert (∀ z, continuity_pt alpha z).
  {
    eapply (piecewise_continuity c alpha (λ t, Rmin x y) (λ t, 2 * t - Rmax x y)).
    { intros. rewrite /alpha. destruct Rle_dec; nra. }
    { intros x'. rewrite /alpha. destruct Rle_dec; try nra.
      intros. assert (c = x') as <- by nra. rewrite /c. nra. }
    { apply continuity_const. intros ?? => //=. }
    { apply continuity_minus.
      { apply continuity_scal. intros ?. apply continuity_pt_id. }
      { apply continuity_const. intros ?? => //=. }
    }
  }
  assert (∀ z, continuity_pt beta z).
  {
    eapply (piecewise_continuity c beta (λ t, Rmax x y) (λ t, 2 * t - Rmin x y)).
    { intros. rewrite /beta. destruct Rle_dec; nra. }
    { intros x'. rewrite /beta. destruct Rle_dec; try nra.
      intros. assert (c = x') as <- by nra. rewrite /c. nra. }
    { apply continuity_const. intros ?? => //=. }
    { apply continuity_minus.
      { apply continuity_scal. intros ?. apply continuity_pt_id. }
      { apply continuity_const. intros ?? => //=. }
    }
  }
 auto with *.
  assert (∀ t, Rmin x y <= t <= Rmax x y -> continuity_pt g t).
  {
    intros. rewrite /g.
    apply continuity_pt_div; last first.
    { rewrite /beta/alpha. destruct Rle_dec => //=; nra. }
    { apply continuity_pt_minus; auto. }
    apply continuity_pt_minus.
    { apply: (continuity_pt_comp beta f'); auto.
      apply continuous_continuity_pt.
      apply: ex_derive_continuous.
      eexists; eapply extension_C1_is_derive; eauto.
      move: Hrange. simpl. apply Rmin_case_strong; apply Rmax_case_strong; nra.
    }
    { apply: (continuity_pt_comp alpha f'); auto.
      apply continuous_continuity_pt.
      apply: ex_derive_continuous.
      eexists; eapply extension_C1_is_derive; eauto.
      move: Hrange. simpl. apply Rmin_case_strong; apply Rmax_case_strong; nra.
    }
  }

Lemma is_derive_Darboux a b g dg:
  (∀ x, a <= x <= b -> is_derive g x (dg x)) ->
  is_Darboux a b dg.
Proof.
  intros Hderiv.
  intros x y v Hrange Hv.
  Search continuity_pt.
  Check continuity_ab_maj.
  set (phi := λ z, g z  - y * z).
  destruct Hv as (Hv1&Hv2).
  destruct Hv1 as [Hv1|Heq]; last first.
  { exists x; split; eauto. apply Rmin_Rmax_l. }
  destruct Hv2 as [Hv2|Heq]; last first.
  { exists y; split; eauto. apply Rmin_Rmax_r. }
  rewrite /is_derive in Hderiv.

  destruct (continuity_ab_maj phi (Rmin x y) (Rmax x y)) as (Mx&HMx&HMx_lb&HMx_ub).
  { admit. }
  { admit. }
*)

Lemma nonneg_derivative_interval_0 (g : R → R) dg a b:
  (∀ x, is_derive g x (dg x)) ->
  (∀ x y, a <= x /\ x <= y /\ y <= b -> g x <= g y) ->
  ∀ x : R, a < x < b -> 0 <= dg x.
Proof.
  intros Hderiv Hincr.
  intros x Hrange.
  set (h := λ x, g (constrain_lb_ub a b x)).
  set (dh := λ x, deriv_constrain_lb_ub a b x * dg (constrain_lb_ub a b x)).
  assert (Hderiv': ∀ x, is_derive h x (dh x)).
  { intros y. rewrite /h/dh.
    apply: is_derive_comp; last auto using deriv_constrain_lb_ub_correct.
    apply Hderiv.
  }
  cut (∀ x, 0 <= dh x).
  { intros Hnn. rewrite /dh in Hnn.
    specialize (Hnn (unconstrain_lb_ub a b x)).
    { rewrite constrain_lb_ub_inv in Hnn; last nra.
      exploit (deriv_constrain_lb_ub_pos a b (unconstrain_lb_ub a b x)); intros; nra.
    }
  }
  intros y.
  rewrite -(is_derive_unique _ _ _ (Hderiv' y)).
  assert (pr: derivable h).
  { intros z. apply ex_derive_Reals_0. eexists; eauto; eapply Hg; eauto. }
  rewrite -(Derive_Reals _ _ (pr y)).
  apply nonneg_derivative_0.
  rewrite /h.
  rewrite /increasing => r s Hle.
  apply Hincr.
  { split.
    apply constrain_lb_ub_spec; nra.
    split; last by (apply constrain_lb_ub_spec; nra).
    apply constrain_lb_ub_increasing; auto. nra.
  }
Qed.


Lemma is_RInt_comp_noncont (f : R -> R) (g dg : R -> R) (a b : R) :
  (ex_RInt f (g a) (g b)) ->
  (forall x y, Rmin a b <= x /\ x <= y /\ y <= Rmax a b -> g x <= g y) ->
  (forall x, Rmin a b <= x <= Rmax a b -> is_derive g x (dg x) /\ continuous dg x) ->
  is_RInt (fun y => scal (dg y) (f (g y))) a b (RInt f (g a) (g b)).
Proof.
  (* We start off the same way is is_RInt_comp proof from Coquelicot *)
  wlog: a b / (a < b) => [Hw|Hab].
    case: (total_order_T a b) => [[Hab'|Hab']|Hab'] Hf Hmono Hg.
    - exact: Hw.
    - rewrite Hab'.
      by rewrite RInt_point; apply: is_RInt_point.
    - rewrite <- (opp_opp (RInt f _ _)).
      apply: is_RInt_swap.
      rewrite opp_RInt_swap //.
        apply Hw => // .
        { by apply ex_RInt_swap. }
        by rewrite Rmin_comm Rmax_comm.
        by rewrite Rmin_comm Rmax_comm.
      rewrite -> Rmin_left by now apply Rlt_le.
      rewrite -> Rmax_right by now apply Rlt_le.

  wlog: g dg / (forall x : R, is_derive g x (dg x) /\ continuous dg x) => [Hw Hf Hmono Hg | Hg Hf Hmono _].
    rewrite -?(extension_C1_ext g dg a b) ; try by [left | right].
    set g0 := extension_C1 g dg a b.
    set dg0 := extension_C0 dg a b.
    apply is_RInt_ext with (fun y : R => scal (dg0 y) (f (g0 y))).
    + rewrite /Rmin /Rmax /g0 ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _ x Hx.
      apply f_equal2.
        by apply extension_C0_ext ; by apply Rlt_le, Hx.
      by apply f_equal, extension_C1_ext ; by apply Rlt_le, Hx.
    + apply Hw.
      * intros x ; split.
        apply extension_C1_is_derive.
          by apply Rlt_le.
            by intros ; apply Hg ; by split.
      * apply @extension_C0_continuous.
          by apply Rlt_le.
        intros ; apply Hg ; by split.
      * intros ; rewrite /g0 ?extension_C1_ext; auto; simpl; try nra.
      * intros ; rewrite /g0 ?extension_C1_ext; auto; simpl; try nra.
    intros ; split.
      apply extension_C1_is_derive.
        by apply Rlt_le.
      intros ; apply Hg ; by split.
    apply @extension_C0_continuous.
      by apply Rlt_le.
    by intros ; apply Hg ; by split.

    have cg : forall x, continuous g x.
      move => t Ht; apply: ex_derive_continuous.
      by exists (dg t); apply Hg.


    assert (g a <= g b).
    { apply (Hmono a b); nra. }

    assert (ex_RInt (λ y : R, scal (dg y) (f (g y))) a b ).
    {
      eapply bounding_ex_RInt'; first nra.
      intros eps.
      edestruct (ex_RInt_bounding f (g a) (g b) eps) as (h1&h2&Hhspec); eauto.

      destruct Hhspec as (Hsandwich&Hh1cont&Hh2cont&Hint_diff).

      exists (λ x, scal (dg x) (h1 (g x))).
      exists (λ x, scal (dg x) (h2 (g x))).

      split.
      intros x Hrange.
      {
         exploit (Hsandwich (g x)).
           { split; eapply Hmono; eauto; try nra. }
           rewrite /scal//=/mult//=.
           destruct (Rle_dec 0 (dg x)); nra.
      }
      split.
      { intros x Hrange.
        apply: continuous_scal.
        { eapply Hg. }
        { eapply continuous_comp; eauto. apply Hh1cont; eauto.
          split; eapply Hmono; eauto; try nra. }
      }
      split.
      { intros x Hrange.
        apply: continuous_scal.
        { eapply Hg. }
        { eapply continuous_comp; eauto. apply Hh2cont; eauto.
          split; eapply Hmono; eauto; try nra. }
      }
      rewrite /scal/=/mult/=.
      eapply (Rle_lt_trans _ (RInt (λ x, (dg x * h2 (g x) - dg x * h1 (g x))) a b)).
      { right. eapply RInt_ext.
        intros x. rewrite Rmin_left ?Rmax_right; try nra.
        intros. apply Rabs_right.
        assert (h1 (g x) <= f (g x) <= h2 (g x)).
        { eapply Hsandwich. split; try apply Hmono; nra. }
        cut (0 <= dg x); first nra.
        eapply nonneg_derivative_interval_0; eauto.
        eapply Hg.
      }
      rewrite RInt_minus.
      { rewrite ?RInt_comp'; try intros x; try nra.
        { rewrite -RInt_minus; auto; apply ex_RInt_continuous; rewrite ?Rmin_left ?Rmax_right //. }
        *  intros; apply Hh1cont. split; eapply Hmono; eauto; try nra.
        *  intros; apply Hg.
        *  intros; apply Hh2cont. split; eapply Hmono; eauto; try nra.
        *  intros; apply Hg.
      }
      * apply: ex_RInt_comp'; eauto; try nra.
        { intros; apply Hh2cont. split; eapply Hmono; eauto; try nra. }
      * apply: ex_RInt_comp'; eauto; try nra.
        { intros; apply Hh1cont. split; eapply Hmono; eauto; try nra. }
    }

Abort.

End comp.
