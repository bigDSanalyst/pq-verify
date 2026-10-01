(* pq-verify: the FIPS 203 and FIPS 204 forward NTT equals the Chinese-
   remainder map it is defined to compute, for EVERY input.

   ML-KEM (FIPS 203, q = 3329, zeta = 17, 7 layers): output coefficients
   (2i, 2i+1) are f mod (X^2 - zeta^(2 BitRev7(i) + 1)).
   ML-DSA (FIPS 204, q = 8380417, zeta = 1753, 8 layers): output
   coefficient i is f(zeta^(2 BitRev8(i) + 1)).

   Method. The transform is written once, generic over its arithmetic
   (add, sub, scale, zero). Any map that commutes with those operations
   commutes with the whole transform (ntt_hom). Running the transform on
   symbolic linear forms -- one per input coefficient -- yields its matrix;
   evaluating a form at an input is such a map. So the transform of ANY
   input is that matrix applied to it, and the matrix is checked entry by
   entry against the CRT matrix computed from the definition above.

   The value-level instance (ops_Z) is the arithmetic of the per-run
   certificates pq-verify emits (pq_verify/core.py, _coq_ntt_prelude). *)

Require Import ZArith Lia List Bool.
Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* Generic transform                                                    *)
(* ------------------------------------------------------------------ *)

(* BEGIN SHARED: pq_verify/core.py emits this block verbatim at the head of
   every per-run NTT certificate, so those certificates compute with exactly
   the transform the theorems below are about. *)
Record Ops (A : Type) := { o_add : A -> A -> A; o_sub : A -> A -> A;
                           o_scale : Z -> A -> A; o_zero : A }.
Arguments o_add {A}. Arguments o_sub {A}. Arguments o_scale {A}. Arguments o_zero {A}.

Fixpoint set_nth {A} (l : list A) (n : nat) (v : A) : list A :=
  match l, n with
  | [], _ => []
  | _ :: t, O => v :: t
  | h :: t, S n' => h :: set_nth t n' v
  end.

Fixpoint brv (k : nat) (x acc : Z) : Z :=
  match k with O => acc | S k' => brv k' (Z.shiftr x 1) (2 * acc + Z.land x 1) end.

Section Transform.
Context {A : Type} (o : Ops A) (zeta : Z -> Z).

Definition bf (f : list A) (j len : nat) (z : Z) : list A :=
  let a := nth j f (o_zero o) in
  let b := nth (j + len)%nat f (o_zero o) in
  let t := o_scale o z b in
  set_nth (set_nth f (j + len)%nat (o_sub o a t)) j (o_add o a t).

Fixpoint inner (f : list A) (j cnt len : nat) (z : Z) : list A :=
  match cnt with O => f | S c => inner (bf f j len z) (S j) c len z end.

Fixpoint groups (f : list A) (start ng len : nat) (k : Z) : list A * Z :=
  match ng with
  | O => (f, k)
  | S g => groups (inner f start len len (zeta k)) (start + 2 * len)%nat g len (k + 1)
  end.

Fixpoint layers (f : list A) (len nl : nat) (k : Z) : list A :=
  match nl with
  | O => f
  | S l => let '(f', k') := groups f 0 (Nat.div 256 (2 * len)) len k in
           layers f' (Nat.div len 2) l k'
  end.

Definition ntt (nl : nat) (f : list A) : list A := layers f 128 nl 1.
End Transform.

Definition ops_mod (q : Z) : Ops Z :=
  {| o_add := fun a t => (a + t) mod q; o_sub := fun a t => (a - t) mod q;
     o_scale := fun z b => (z * b) mod q; o_zero := 0 |}.
(* END SHARED *)

(* ------------------------------------------------------------------ *)
(* Any operation-preserving map commutes with the transform            *)
(* ------------------------------------------------------------------ *)

Section Hom.
Context {A B : Type} (oa : Ops A) (ob : Ops B) (h : A -> B) (zeta : Z -> Z).
Hypothesis h_add : forall x y, h (o_add oa x y) = o_add ob (h x) (h y).
Hypothesis h_sub : forall x y, h (o_sub oa x y) = o_sub ob (h x) (h y).
Hypothesis h_scale : forall z x, h (o_scale oa z x) = o_scale ob z (h x).
Hypothesis h_zero : h (o_zero oa) = o_zero ob.

Lemma map_set_nth : forall l n v, map h (set_nth l n v) = set_nth (map h l) n (h v).
Proof. induction l; intros [|n] v; simpl; f_equal; auto. Qed.

Lemma h_nth : forall l n, h (nth n l (o_zero oa)) = nth n (map h l) (o_zero ob).
Proof. intros. rewrite <- h_zero. symmetry. apply map_nth. Qed.

Lemma bf_hom : forall f j len z, map h (bf oa f j len z) = bf ob (map h f) j len z.
Proof.
  intros. unfold bf. rewrite !map_set_nth, h_add, h_sub, h_scale, !h_nth. reflexivity.
Qed.

Lemma inner_hom : forall cnt f j len z,
  map h (inner oa f j cnt len z) = inner ob (map h f) j cnt len z.
Proof. induction cnt; intros; simpl; [reflexivity|]. rewrite IHcnt, bf_hom. reflexivity. Qed.

Lemma groups_hom : forall ng f start len k,
  map h (fst (groups oa zeta f start ng len k)) = fst (groups ob zeta (map h f) start ng len k)
  /\ snd (groups oa zeta f start ng len k) = snd (groups ob zeta (map h f) start ng len k).
Proof.
  induction ng; intros; simpl; [auto|].
  destruct (IHng (inner oa f start len len (zeta k)) (start + 2 * len)%nat len (k + 1)) as [H1 H2].
  rewrite inner_hom in H1, H2. auto.
Qed.

Lemma layers_hom : forall nl f len k,
  map h (layers oa zeta f len nl k) = layers ob zeta (map h f) len nl k.
Proof.
  induction nl; intros; cbn [layers]; [reflexivity|].
  destruct (groups_hom (Nat.div 256 (2 * len)) f 0 len k) as [H1 H2].
  destruct (groups oa zeta f 0 (Nat.div 256 (2 * len)) len k) as [fa ka] eqn:Ea.
  destruct (groups ob zeta (map h f) 0 (Nat.div 256 (2 * len)) len k) as [fb kb] eqn:Eb.
  simpl in H1, H2. subst. rewrite IHnl. reflexivity.
Qed.

Theorem ntt_hom : forall nl f, map h (ntt oa zeta nl f) = ntt ob zeta nl (map h f).
Proof. intros. apply layers_hom. Qed.
End Hom.

(* ------------------------------------------------------------------ *)
(* The two instances: field elements, and linear forms over 256 inputs  *)
(* ------------------------------------------------------------------ *)

Section Instances.
Variable q : Z.
Hypothesis q_pos : 0 < q.

Definition ops_Z : Ops Z := ops_mod q.

Definition idx := seq 0 256.
Definition pw (g : Z -> Z -> Z) (u v : list Z) : list Z :=
  map (fun j => g (nth j u 0) (nth j v 0)) idx.

Definition ops_F : Ops (list Z) :=
  {| o_add := pw (fun x y => (x + y) mod q); o_sub := pw (fun x y => (x - y) mod q);
     o_scale := fun z u => map (fun j => (z * nth j u 0) mod q) idx;
     o_zero := repeat 0 256 |}.

Fixpoint sumZ (l : list Z) : Z := match l with [] => 0 | x :: t => x + sumZ t end.

(* evaluate the linear form u at the input F *)
Definition ev (F : nat -> Z) (u : list Z) : Z :=
  sumZ (map (fun j => nth j u 0 * F j) idx) mod q.

Lemma nth_idx_map : forall (g : nat -> Z) j, (j < 256)%nat -> nth j (map g idx) 0 = g j.
Proof.
  intros g j Hj. unfold idx.
  rewrite (nth_indep _ 0 (g 0%nat)) by (rewrite map_length, seq_length; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

Lemma sum_congr : forall L (a b : nat -> Z),
  (forall j, In j L -> a j mod q = b j mod q) ->
  sumZ (map a L) mod q = sumZ (map b L) mod q.
Proof.
  induction L as [|x L IHL]; intros a b H; simpl; [reflexivity|].
  rewrite Z.add_mod, (Z.add_mod (b x)) by lia.
  rewrite H by (left; reflexivity). rewrite (IHL a b) by (intros; apply H; right; auto).
  reflexivity.
Qed.

Lemma sum_add : forall L (a b : nat -> Z),
  sumZ (map (fun j => a j + b j) L) = sumZ (map a L) + sumZ (map b L).
Proof. induction L; intros; simpl; [reflexivity|]. rewrite IHL. ring. Qed.

Lemma sum_sub : forall L (a b : nat -> Z),
  sumZ (map (fun j => a j - b j) L) = sumZ (map a L) - sumZ (map b L).
Proof. induction L; intros; simpl; [reflexivity|]. rewrite IHL. ring. Qed.

Lemma sum_scale : forall L (z : Z) (a : nat -> Z),
  sumZ (map (fun j => z * a j) L) = z * sumZ (map a L).
Proof. induction L; intros; simpl; [ring|]. rewrite IHL. ring. Qed.

Lemma in_idx : forall j, In j idx -> (j < 256)%nat.
Proof. intros j H. unfold idx in H. apply in_seq in H. lia. Qed.

Lemma ev_add : forall F u v, ev F (o_add ops_F u v) = o_add ops_Z (ev F u) (ev F v).
Proof.
  intros. unfold ev, ops_F, ops_Z, ops_mod; cbn [o_add o_sub o_scale o_zero]. unfold pw.
  rewrite (sum_congr _ _ (fun j => nth j u 0 * F j + nth j v 0 * F j)).
  - rewrite sum_add, <- Z.add_mod by lia. reflexivity.
  - intros j Hj. rewrite nth_idx_map by (apply in_idx; auto).
    rewrite Z.mul_mod_idemp_l by lia. f_equal. ring.
Qed.

Lemma ev_sub : forall F u v, ev F (o_sub ops_F u v) = o_sub ops_Z (ev F u) (ev F v).
Proof.
  intros. unfold ev, ops_F, ops_Z, ops_mod; cbn [o_add o_sub o_scale o_zero]. unfold pw.
  rewrite (sum_congr _ _ (fun j => nth j u 0 * F j - nth j v 0 * F j)).
  - rewrite sum_sub. apply Zminus_mod.
  - intros j Hj. rewrite nth_idx_map by (apply in_idx; auto).
    rewrite Z.mul_mod_idemp_l by lia. f_equal. ring.
Qed.

Lemma ev_scale : forall F z u, ev F (o_scale ops_F z u) = o_scale ops_Z z (ev F u).
Proof.
  intros. unfold ev, ops_F, ops_Z, ops_mod; cbn [o_add o_sub o_scale o_zero].
  rewrite (sum_congr _ _ (fun j => z * (nth j u 0 * F j))).
  - rewrite sum_scale, Z.mul_mod_idemp_r by lia. reflexivity.
  - intros j Hj. rewrite nth_idx_map by (apply in_idx; auto).
    rewrite Z.mul_mod_idemp_l by lia. f_equal. ring.
Qed.

Lemma ev_zero : forall F, ev F (o_zero ops_F) = o_zero ops_Z.
Proof.
  intros. unfold ev, ops_F, ops_Z, ops_mod; cbn [o_add o_sub o_scale o_zero].
  rewrite (sum_congr _ _ (fun _ => 0)).
  - assert (forall L, sumZ (map (fun _ : nat => 0) L) = 0) as S
      by (induction L; simpl; auto). rewrite S. reflexivity.
  - intros j Hj. rewrite nth_repeat. reflexivity.
Qed.

(* reduction mod q also commutes with the value arithmetic *)
Definition modq (x : Z) : Z := x mod q.
Lemma modq_add : forall x y, modq (o_add ops_Z x y) = o_add ops_Z (modq x) (modq y).
Proof. intros. unfold modq, ops_Z, ops_mod; cbn [o_add o_sub o_scale o_zero]. rewrite Z.mod_mod by lia. apply Z.add_mod; lia. Qed.
Lemma modq_sub : forall x y, modq (o_sub ops_Z x y) = o_sub ops_Z (modq x) (modq y).
Proof. intros. unfold modq, ops_Z, ops_mod; cbn [o_add o_sub o_scale o_zero]. rewrite Z.mod_mod by lia. apply Zminus_mod. Qed.
Lemma modq_scale : forall z x, modq (o_scale ops_Z z x) = o_scale ops_Z z (modq x).
Proof. intros. unfold modq, ops_Z, ops_mod; cbn [o_add o_sub o_scale o_zero]. rewrite Z.mod_mod by lia. symmetry. apply Z.mul_mod_idemp_r; lia. Qed.
Lemma modq_zero : modq (o_zero ops_Z) = o_zero ops_Z.
Proof. unfold modq, ops_Z, ops_mod; cbn [o_add o_sub o_scale o_zero]. apply Z.mod_0_l. lia. Qed.

(* the input coefficient j as a linear form *)
Definition unit (j : nat) : list Z := map (fun i => if Nat.eqb i j then 1 else 0) idx.
Definition basis : list (list Z) := map unit idx.

Lemma sum_unit : forall L (F : nat -> Z) j,
  NoDup L -> In j L ->
  sumZ (map (fun i => (if Nat.eqb i j then 1 else 0) * F i) L) = F j.
Proof.
  induction L as [|a L IH]; intros F j ND Hin; [destruct Hin|].
  inversion ND as [|? ? Hna ND']; subst. simpl.
  destruct (Nat.eqb_spec a j) as [->|Hne].
  - assert (forall L', ~ In j L' ->
        sumZ (map (fun i => (if Nat.eqb i j then 1 else 0) * F i) L') = 0) as Z0.
    { induction L'; intros Hn; simpl; [reflexivity|].
      destruct (Nat.eqb_spec a j); [subst; exfalso; apply Hn; left; auto|].
      rewrite IHL' by (intro; apply Hn; right; auto). ring. }
    rewrite Z0 by auto. ring.
  - destruct Hin as [->|Hin]; [contradiction|]. rewrite IH by auto. ring.
Qed.

Lemma ev_unit : forall F j, (j < 256)%nat -> ev F (unit j) = F j mod q.
Proof.
  intros F j Hj. unfold ev, unit.
  rewrite (map_ext_in _ (fun i => (if Nat.eqb i j then 1 else 0) * F i)).
  - rewrite sum_unit; [reflexivity | apply seq_NoDup | apply in_seq; lia].
  - intros i Hi. rewrite nth_idx_map by (apply in_idx; auto). reflexivity.
Qed.

Lemma list_as_idx : forall (f : list Z), length f = 256%nat ->
  map modq f = map (fun j => nth j f 0 mod q) idx.
Proof.
  intros f Hl. apply nth_ext with (d := 0) (d' := 0).
  - rewrite !map_length. unfold idx. rewrite seq_length. auto.
  - intros n Hn. rewrite map_length in Hn.
    rewrite nth_idx_map by lia.
    rewrite (nth_indep _ 0 (modq 0)) by (rewrite map_length; lia).
    rewrite map_nth. reflexivity.
Qed.

(* For every input f of 256 coefficients: reducing NTT(f) mod q gives the
   matrix M applied to f, where M = NTT of the 256 unit forms. *)
Theorem ntt_is_matrix : forall zeta nl (f : list Z), length f = 256%nat ->
  map modq (ntt ops_Z zeta nl f)
  = map (ev (fun j => nth j f 0)) (ntt ops_F zeta nl basis).
Proof.
  intros zeta nl f Hl.
  rewrite (ntt_hom ops_Z ops_Z modq zeta modq_add modq_sub modq_scale modq_zero).
  rewrite list_as_idx by auto.
  replace (map (fun j => nth j f 0 mod q) idx)
    with (map (ev (fun j => nth j f 0)) basis).
  - symmetry. apply (ntt_hom ops_F ops_Z _ zeta (ev_add _) (ev_sub _) (ev_scale _) (ev_zero _)).
  - unfold basis. rewrite map_map. apply map_ext_in. intros j Hj.
    apply ev_unit, in_idx; auto.
Qed.
End Instances.

(* ------------------------------------------------------------------ *)
(* FIPS 203: ML-KEM                                                     *)
(* ------------------------------------------------------------------ *)

Definition kq := 3329.
Definition kzeta (i : Z) : Z := Z.modulo (17 ^ brv 7 i 0) kq.

Fixpoint powers (g : Z) (n : nat) (acc : Z) : list Z :=
  match n with O => [] | S m => acc :: powers g m (acc * g mod kq) end.

(* f mod (X^2 - gamma): coefficient 0 collects the even powers, 1 the odd *)
Definition kem_rows (i : nat) : list (list Z) :=
  let g := Z.modulo (17 ^ (2 * brv 7 (Z.of_nat i) 0 + 1)) kq in
  let p := powers g 128 1 in
  [ map (fun j => if Nat.even j then nth (Nat.div j 2) p 0 else 0) (seq 0 256);
    map (fun j => if Nat.even j then 0 else nth (Nat.div j 2) p 0) (seq 0 256) ].

Definition kem_crt : list (list Z) := flat_map kem_rows (seq 0 128).

Lemma kem_matrix : ntt (ops_F kq) kzeta 7 basis = kem_crt.
Proof. vm_compute. reflexivity. Qed.

Theorem mlkem_ntt_correct : forall f : list Z, length f = 256%nat ->
  map (fun x => x mod kq) (ntt (ops_Z kq) kzeta 7 f)
  = map (ev kq (fun j => nth j f 0)) kem_crt.
Proof.
  intros f Hl. rewrite <- kem_matrix.
  apply (ntt_is_matrix kq ltac:(unfold kq; lia)). auto.
Qed.

(* ------------------------------------------------------------------ *)
(* FIPS 204: ML-DSA                                                     *)
(* ------------------------------------------------------------------ *)

Definition dq := 8380417.
Definition dzeta (i : Z) : Z := Z.modulo (1753 ^ brv 8 i 0) dq.

Fixpoint dpowers (g : Z) (n : nat) (acc : Z) : list Z :=
  match n with O => [] | S m => acc :: dpowers g m (acc * g mod dq) end.

(* f evaluated at gamma_i = zeta^(2 BitRev8(i) + 1) *)
Definition dsa_crt : list (list Z) :=
  map (fun i => dpowers (Z.modulo (1753 ^ (2 * brv 8 (Z.of_nat i) 0 + 1)) dq) 256 1)
      (seq 0 256).

Lemma dsa_matrix : ntt (ops_F dq) dzeta 8 basis = dsa_crt.
Proof. vm_compute. reflexivity. Qed.

Theorem mldsa_ntt_correct : forall f : list Z, length f = 256%nat ->
  map (fun x => x mod dq) (ntt (ops_Z dq) dzeta 8 f)
  = map (ev dq (fun j => nth j f 0)) dsa_crt.
Proof.
  intros f Hl. rewrite <- dsa_matrix.
  apply (ntt_is_matrix dq ltac:(unfold dq; lia)). auto.
Qed.

Print Assumptions mlkem_ntt_correct.
Print Assumptions mldsa_ntt_correct.
