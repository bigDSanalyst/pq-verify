(* pq-verify: modular reductions of the ML-KEM and ML-DSA reference code,
   proved correct for EVERY input in their documented range.

   These are general theorems, not computed instances: each statement
   quantifies over all integers a in the range the C code admits. The
   right shifts of the C code are floor division by a power of two, which
   is what Z.div is.

     montgomery_reduce (ML-KEM, R = 2^16, int32 input, int16 output)
     montgomery_reduce (ML-DSA, R = 2^32, int64 input, int32 output)
     barrett_reduce    (ML-KEM, int16 input; exhaustive)
     reduce32          (ML-DSA)

   Sources: pq-crystals/kyber ref/reduce.c, pq-crystals/dilithium ref/reduce.c *)

Require Import ZArith Lia List.
Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* Montgomery reduction, general                                        *)
(* ------------------------------------------------------------------ *)

(* The signed low half of x: the value of (intK_t)x in C, in [-R/2, R/2). *)
Definition cmod (x R : Z) : Z := (x + R / 2) mod R - R / 2.

(* montgomery_reduce: t = (intK_t)(a * QINV); return (a - t*q) >> log2 R *)
Definition mont (q R qinv a : Z) : Z := (a - cmod (a * qinv) R * q) / R.

Lemma cmod_congr : forall x R, R > 0 -> exists k, cmod x R = x - R * k.
Proof.
  intros x R HR. unfold cmod.
  exists ((x + R / 2) / R).
  pose proof (Z.div_mod (x + R / 2) R ltac:(lia)). lia.
Qed.

Lemma cmod_range : forall x R, R > 0 -> Z.even R = true ->
  - (R / 2) <= cmod x R < R / 2.
Proof.
  intros x R HR He. unfold cmod.
  pose proof (Z.mod_pos_bound (x + R / 2) R ltac:(lia)).
  apply Zeven_bool_iff, Zeven_ex in He. destruct He as [h Hh]. subst R.
  assert (Hd : 2 * h / 2 = h) by (rewrite Z.mul_comm; apply Z.div_mul; lia).
  rewrite Hd in *. lia.
Qed.

(* The subtraction is exactly divisible by R, so the shift loses nothing,
   and the result is a * R^-1 modulo q. *)
Theorem mont_exact : forall q R qinv a,
  R > 0 -> (q * qinv) mod R = 1 ->
  R * mont q R qinv a = a - cmod (a * qinv) R * q.
Proof.
  intros q R qinv a HR Hinv. unfold mont.
  destruct (cmod_congr (a * qinv) R HR) as [s Hs]. rewrite Hs.
  pose proof (Z.div_mod (q * qinv) R ltac:(lia)) as Hj. rewrite Hinv in Hj.
  set (j := q * qinv / R) in *.
  assert (E : a - (a * qinv - R * s) * q = R * (s * q - a * j)).
  { replace ((a * qinv - R * s) * q) with (a * (q * qinv) - R * s * q) by ring.
    rewrite Hj. ring. }
  rewrite E. f_equal. rewrite Z.mul_comm. apply Z.div_mul. lia.
Qed.

Theorem mont_congruent : forall q R qinv a,
  R > 0 -> (q * qinv) mod R = 1 ->
  (R * mont q R qinv a - a) mod q = 0.
Proof.
  intros q R qinv a HR Hinv. rewrite (mont_exact q R qinv a HR Hinv).
  replace (a - cmod (a * qinv) R * q - a) with ((- cmod (a * qinv) R) * q) by ring.
  apply Z.mod_mul. intro; subst q. rewrite Z.mul_0_l, Z.mod_0_l in Hinv; lia.
Qed.

(* ---- ML-KEM: q = 3329, R = 2^16, QINV = -3327 ---------------------- *)

Definition KQ := 3329.
Definition KQINV := -3327.

Theorem mlkem_qinv : (KQ * KQINV) mod 2^16 = 1.
Proof. vm_compute. reflexivity. Qed.

(* For every int32 a in {-q2^15, ..., q2^15 - 1} (the range ref/reduce.c
   documents): montgomery_reduce(a) * 2^16 = a (mod q), -q < result < q. *)
Theorem mlkem_montgomery_reduce : forall a,
  - (KQ * 2^15) <= a <= KQ * 2^15 - 1 ->
  (2^16 * mont KQ (2^16) KQINV a - a) mod KQ = 0 /\
  - KQ < mont KQ (2^16) KQINV a < KQ.
Proof.
  intros a Ha. split.
  - apply mont_congruent; [lia | exact mlkem_qinv].
  - pose proof (mont_exact KQ (2^16) KQINV a ltac:(lia) mlkem_qinv) as E.
    pose proof (cmod_range (a * KQINV) (2^16) ltac:(lia) eq_refl) as C.
    unfold KQ in *.
    change (2^16) with 65536 in *. change (2^15) with 32768 in *.
    change (65536 / 2) with 32768 in *. lia.
Qed.

(* The intermediate a - t*q fits in int32 (no overflow in the C code). *)
Theorem mlkem_montgomery_no_overflow : forall a,
  - (KQ * 2^15) <= a <= KQ * 2^15 ->
  - 2^31 <= a - cmod (a * KQINV) (2^16) * KQ < 2^31.
Proof.
  intros a Ha. pose proof (cmod_range (a * KQINV) (2^16) ltac:(lia) eq_refl) as C.
  unfold KQ in *.
    change (2^16) with 65536 in *. change (2^15) with 32768 in *.
    change (65536 / 2) with 32768 in *. lia.
Qed.

(* ---- ML-DSA: q = 8380417, R = 2^32, QINV = 58728449 ------------------ *)

Definition DQ := 8380417.
Definition DQINV := 58728449.

Theorem mldsa_qinv : (DQ * DQINV) mod 2^32 = 1.
Proof. vm_compute. reflexivity. Qed.

(* For every int64 a in [-q2^31, q2^31 - 1]: result * 2^32 = a (mod q),
   and -q < result < q.

   ref/reduce.c documents the input range as -2^31 Q <= a <= Q 2^31,
   inclusive. At the single input a = Q 2^31 the result is Q itself, so the
   documented "-Q < r < Q" does not hold there (mldsa_montgomery_top_input
   below). Every input ML-DSA actually feeds it is a product of reduced
   values, |a| < Q^2, far inside the range, so no output is affected. *)
Theorem mldsa_montgomery_reduce : forall a,
  - (DQ * 2^31) <= a <= DQ * 2^31 - 1 ->
  (2^32 * mont DQ (2^32) DQINV a - a) mod DQ = 0 /\
  - DQ < mont DQ (2^32) DQINV a < DQ.
Proof.
  intros a Ha. split.
  - apply mont_congruent; [lia | exact mldsa_qinv].
  - pose proof (mont_exact DQ (2^32) DQINV a ltac:(lia) mldsa_qinv) as E.
    pose proof (cmod_range (a * DQINV) (2^32) ltac:(lia) eq_refl) as C.
    unfold DQ in *.
    change (2^32) with 4294967296 in *. change (2^31) with 2147483648 in *.
    change (2^63) with 9223372036854775808 in *.
    change (4294967296 / 2) with 2147483648 in *. lia.
Qed.

Theorem mldsa_montgomery_top_input : mont DQ (2^32) DQINV (DQ * 2^31) = DQ.
Proof. vm_compute. reflexivity. Qed.

(* ML-KEM's documented range stops at q2^15 - 1 for exactly this reason:
   at q2^15 the result would be q. *)
Theorem mlkem_montgomery_top_input : mont KQ (2^16) KQINV (KQ * 2^15) = KQ.
Proof. vm_compute. reflexivity. Qed.

Theorem mldsa_montgomery_no_overflow : forall a,
  - (DQ * 2^31) <= a <= DQ * 2^31 ->
  - 2^63 <= a - cmod (a * DQINV) (2^32) * DQ < 2^63.
Proof.
  intros a Ha. pose proof (cmod_range (a * DQINV) (2^32) ltac:(lia) eq_refl) as C.
  unfold DQ in *.
    change (2^32) with 4294967296 in *. change (2^31) with 2147483648 in *.
    change (2^63) with 9223372036854775808 in *.
    change (4294967296 / 2) with 2147483648 in *. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* ML-KEM barrett_reduce, exhaustive over all 65,536 int16 inputs       *)
(* ------------------------------------------------------------------ *)

(* v = ((1<<26) + q/2) / q = 20159; t = (v*a + (1<<25)) >> 26; a - t*q *)
Definition barrett (a : Z) : Z :=
  a - ((20159 * a + 2^25) / 2^26) * KQ.

Definition barrett_ok (a : Z) : bool :=
  ((barrett a - a) mod KQ =? 0) && (-1664 <=? barrett a) && (barrett a <=? 1664).

Fixpoint check_from (a : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S m => barrett_ok a && check_from (a + 1) m
  end.

Lemma check_from_sound : forall n a x,
  check_from a n = true -> a <= x < a + Z.of_nat n -> barrett_ok x = true.
Proof.
  induction n as [|n IH]; intros a x H Hx; simpl in *.
  - lia.
  - apply andb_prop in H as [H1 H2].
    destruct (Z.eq_dec x a) as [->|Hne]; [exact H1|].
    apply (IH (a + 1)); [exact H2|lia].
Qed.

Lemma barrett_all : check_from (-32768) 65536 = true.
Proof. vm_compute. reflexivity. Qed.

(* For every int16 a: barrett_reduce(a) = a (mod q), centred in
   [-(q-1)/2, (q-1)/2]. *)
Theorem mlkem_barrett_reduce : forall a,
  -32768 <= a <= 32767 ->
  (barrett a - a) mod KQ = 0 /\ -1664 <= barrett a <= 1664.
Proof.
  intros a Ha.
  assert (N : Z.of_nat 65536 = 65536) by (vm_compute; reflexivity).
  pose proof (check_from_sound 65536 (-32768) a barrett_all ltac:(rewrite N; lia)) as H.
  unfold barrett_ok in H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* ML-DSA reduce32                                                      *)
(* ------------------------------------------------------------------ *)

(* t = (a + (1<<22)) >> 23; return a - t*Q *)
Definition reduce32 (a : Z) : Z := a - ((a + 2^22) / 2^23) * DQ.

(* For every int32 a <= 2^31 - 2^22 - 1: reduce32(a) = a (mod q) and
   -6283009 <= reduce32(a) <= 6283008.

   ref/reduce.c documents -6283008 <= r <= 6283008. The lower bound is one
   too high: at a = -255 * 2^23 - 2^22 the result is -6283009
   (mldsa_reduce32_lower_witness). The upper bound is exact. *)
Theorem mldsa_reduce32 : forall a,
  - 2^31 <= a <= 2^31 - 2^22 - 1 ->
  (reduce32 a - a) mod DQ = 0 /\ -6283009 <= reduce32 a <= 6283008.
Proof.
  intros a Ha. unfold reduce32. split.
  - replace (a - (a + 2 ^ 22) / 2 ^ 23 * DQ - a)
      with (- ((a + 2 ^ 22) / 2 ^ 23) * DQ) by ring.
    apply Z.mod_mul. unfold DQ; lia.
  - change (2^22) with 4194304 in *. change (2^23) with 8388608 in *.
    change (2^31) with 2147483648 in *.
    pose proof (Z.div_mod (a + 4194304) 8388608 ltac:(lia)).
    pose proof (Z.mod_pos_bound (a + 4194304) 8388608 ltac:(lia)).
    unfold DQ. lia.
Qed.

Theorem mldsa_reduce32_lower_witness :
  reduce32 (-255 * 2^23 - 2^22) = -6283009.
Proof. vm_compute. reflexivity. Qed.

Theorem mldsa_reduce32_upper_attained :
  exists a, - 2^31 <= a <= 2^31 - 2^22 - 1 /\ reduce32 a = 6283008.
Proof. exists (2^31 - 2^22 - 1). split; [lia | vm_compute; reflexivity]. Qed.

Print Assumptions mlkem_montgomery_reduce.
Print Assumptions mlkem_montgomery_no_overflow.
Print Assumptions mldsa_montgomery_reduce.
Print Assumptions mldsa_montgomery_no_overflow.
Print Assumptions mlkem_barrett_reduce.
Print Assumptions mldsa_reduce32.
Print Assumptions mldsa_reduce32_lower_witness.
Print Assumptions mldsa_montgomery_top_input.
Print Assumptions mlkem_montgomery_top_input.
