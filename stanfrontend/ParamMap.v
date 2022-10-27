
Require Import Zwf.
Require Import Axioms.
Require Import Coqlib.
Require Intv.
Require Import Maps.
Require Archi.
Require Import AST.
Require Import Integers.
Require Import ssreflect.
Require Import Floats.
Require Import Values.
Require Export Memdata.
Require Export Memtype.

Local Set Implicit Arguments.

Section param_mem.

Context {A : Type}.

Definition param_mem := PTree.t (ZTree.t A).

Definition empty := PTree.empty (ZTree.t A).

Definition is_id_alloc (pm : param_mem) id : bool :=
  match pm ! id with
  | Some _ => true
  | _ => false
  end.

Definition get (pm: param_mem) (id: ident) (ofs: Z) : option A :=
  match pm ! id with
  | Some zm => ZTree.get ofs zm
  | _ => None
  end.

Definition reserve (pm: param_mem) (id: ident) : param_mem :=
  match pm ! id with
  | Some zm => pm
  | _ => PTree.set id (ZTree.empty _) pm
  end.

(* Set "allocates" and stores *)
Definition set (pm: param_mem) (id: ident) (ofs: Z) (f : A) : param_mem :=
  match pm ! id with
  | Some zm =>
      let zm := ZTree.set ofs f zm in
      PTree.set id zm pm
  | _ =>
      let zm := ZTree.set ofs f (ZTree.empty A) in
      PTree.set id zm pm
  end.

(* Set "allocates" and stores id from offset 1 to sz *)
Fixpoint setv (pm: param_mem) (id: ident) (sz: nat) (f : A) : param_mem :=
  match sz with
  | O => reserve pm id
  | S n' => setv (set pm id (Z.of_nat sz) f) id n' f
end.

Definition store (pm: param_mem) (id: ident) (ofs: Z) (f : A) : option param_mem :=
  match pm ! id with
  | Some zm =>
      match ZTree.get ofs zm with
      | None => None
      | Some _ =>
          let zm := ZTree.set ofs f zm in
          Some (PTree.set id zm pm)
      end
  | _ => None
  end.

Lemma gs_is_alloc pm id ofs f :
  get pm id ofs = Some f -> is_id_alloc pm id = true.
Proof.
  unfold get, is_id_alloc. destruct (pm ! id); try congruence.
Qed.

Lemma reserve_is_alloc pm pm' id :
  reserve pm id = pm' -> is_id_alloc pm' id = true.
Proof.
  unfold reserve, is_id_alloc; intros <-; destruct (pm ! id) as [s|] eqn:Heq; simpl; try congruence.
  - rewrite Heq. auto.
  - rewrite PTree.gss; auto.
Qed.

Lemma reserve_preserves_alloc_rev pm pm' id id':
  reserve pm id = pm' -> is_id_alloc pm' id' = false -> is_id_alloc pm id' = false.
Proof.
  unfold reserve, is_id_alloc; intros <-.
  destruct (pm ! id) as [s|] eqn:Heq; simpl; try congruence.
  destruct (pm ! id') as [s|] eqn:Heq'; simpl; try congruence.
  assert (id <> id') by congruence.
  rewrite PTree.gso; auto. rewrite Heq'. auto.
Qed.

Lemma set_preserves_alloc_rev pm pm' id ofs v id':
  set pm id ofs v  = pm' -> is_id_alloc pm' id' = false -> is_id_alloc pm id' = false.
Proof.
  unfold set, is_id_alloc; intros <-.
  destruct (pm ! id) as [?|] eqn:Heq; simpl; try congruence.
  {
    destruct (pm ! id') as [?|] eqn:Heq'; simpl; try congruence.
    destruct (Pos.eq_dec id id'); subst.
    { rewrite PTree.gss; auto. }
    { rewrite PTree.gso; auto. rewrite Heq'; auto. }
  }
  destruct (Pos.eq_dec id id'); subst.
  { rewrite Heq; auto. }
  { rewrite PTree.gso; auto. }
Qed.


Lemma gr pm id1 id2 ofs :
  get (reserve pm id1) id2 ofs = get pm id2 ofs.
Proof.
  unfold reserve, get.
  destruct (pm ! id1) as [|] eqn:Heq1; simpl; try congruence.
  destruct (pm ! id2) as [|] eqn:Heq2; simpl; try congruence.
  { destruct (Pos.eq_dec id1 id2); try congruence.
    rewrite PTree.gso ?Heq2; auto.
  }
  { destruct (Pos.eq_dec id1 id2); try congruence.
    * subst. rewrite PTree.gss ?Heq2; auto.
    * rewrite PTree.gso ?Heq2; auto.
  }
Qed.

Lemma gr_some pm pm' id ofs f :
  get pm id ofs = Some f ->
  reserve pm id = pm' ->
  get pm' id ofs = Some f.
Proof. intros Hget <-. rewrite gr //. Qed.

Lemma gss pm id ofs v :
  get (set pm id ofs v) id ofs = Some v.
Proof.
  unfold get, set.
  destruct (pm ! id) as [|] eqn:Hpm.
  { rewrite PTree.gss ZTree.gss //. }
  { rewrite PTree.gss ZTree.gss //. }
Qed.

Lemma gso pm id ofs id' ofs' v :
  (id' <> id \/ ofs' <> ofs) ->
  get (set pm id ofs v) id' ofs' = get pm id' ofs'.
Proof.
  unfold get, set. intros Hneq.
  destruct (pm ! id) as [|] eqn:Hpm.
  {
    destruct (Pos.eq_dec id' id); subst.
    { destruct Hneq; first by congruence.
      rewrite PTree.gss ZTree.gso; auto.
      rewrite Hpm //. }
    rewrite PTree.gso //. }
  {
    destruct (Pos.eq_dec id' id); subst.
    { destruct Hneq; first by congruence.
      rewrite PTree.gss ZTree.gso; auto.
      rewrite Hpm //. }
    rewrite PTree.gso //. }
Qed.

Lemma is_id_set_other id id' pm o v :
  id' <> id -> is_id_alloc (set pm id o v) id' = is_id_alloc pm id'.
Proof.
  intros Hneq. rewrite /is_id_alloc/set.
  destruct (pm ! id) as [|] eqn:Hpm.
  {
    destruct (Pos.eq_dec id' id); subst.
    { destruct Hneq; first by congruence. }
    rewrite PTree.gso //. }
  {
    destruct (Pos.eq_dec id' id); subst.
    { destruct Hneq; first by congruence. }
    rewrite PTree.gso //. }
Qed.

Lemma is_id_reserve_other id id' pm :
  id' <> id -> is_id_alloc (reserve pm id) id' = is_id_alloc pm id'.
Proof.
  rewrite /is_id_alloc/reserve.
  destruct (pm ! id) as [|] eqn:Hpm.
  {
    destruct (pm ! id') as [|] eqn:Hpm'; auto.
  }
  {
    intros Hneq. rewrite PTree.gso; auto.
  }
Qed.

Lemma is_id_reserve_same id pm :
  is_id_alloc (reserve pm id) id = true.
Proof.
  rewrite /is_id_alloc/reserve.
  destruct (pm ! id) as [|] eqn:Hpm.
  { rewrite Hpm. auto. }
  { rewrite PTree.gss; auto. }
Qed.

Lemma is_id_set_same id pm o v :
  is_id_alloc (set pm id o v) id = true.
Proof.
  rewrite /is_id_alloc/set.
  destruct (pm ! id) as [|] eqn:Hpm.
  { rewrite PTree.gss //. }
  { rewrite PTree.gss //. }
Qed.

Lemma is_id_setv_same id pm v n :
  is_id_alloc (setv pm id n v) id = true.
Proof.
  revert pm.
  induction n => pm.
  { rewrite is_id_reserve_same //. }
  { rewrite IHn; auto. }
Qed.

Lemma is_id_setv_other id id' pm v n :
  id' <> id ->
  is_id_alloc (setv pm id n v) id' =  is_id_alloc pm id'.
Proof.
  revert pm.
  induction n => pm.
  { intros. rewrite is_id_reserve_other //. }
  { intros. rewrite IHn; auto. rewrite is_id_set_other //. }
Qed.

Lemma is_id_empty id :
  is_id_alloc empty id = false.
Proof.
  rewrite /is_id_alloc. rewrite PTree.gempty //.
Qed.

Lemma gempty id ofs :
  get empty id ofs = None.
Proof.
  rewrite /get/empty. rewrite PTree.gempty //.
Qed.

Lemma store_some_is_id_alloc m id ofs v m' :
  store m id ofs v = Some m' ->
  is_id_alloc m id = true /\ is_id_alloc m' id = true.
Proof.
  rewrite /store/is_id_alloc.
  destruct (m ! id); try congruence.
  destruct (ZTree.get _ _); try congruence.
  inversion 1; subst; split; auto.
  rewrite PTree.gss //.
Qed.

Lemma store_same_is_id_alloc m id id' ofs v m' :
  store m id ofs v = Some m' ->
  is_id_alloc m' id' = is_id_alloc m id'.
Proof.
  rewrite /store/is_id_alloc.
  destruct (m ! id) eqn:Hlook; try congruence.
  destruct (ZTree.get _ _); try congruence.
  inversion 1; subst.
  destruct (Pos.eq_dec id id').
  { subst. rewrite PTree.gss // Hlook. auto. }
  { rewrite PTree.gso //. congruence. }
Qed.

End param_mem.

Global Arguments param_mem  _ : clear implicits.
Global Arguments empty  _ : clear implicits.
