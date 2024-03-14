Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Open Scope Z_scope.

Record affine_key := {
  a : Z;
  b : Z;
  a_inv : Z;
  a_inv_correct : a * a_inv mod 26 = 1;
  gcd_a_26 : Z.gcd a 26 = 1
}.

(* For a = 1 and a_inv = 1, we can fill in the proofs directly. *)

Definition test_affine_key : affine_key := {|
  a := 1;
  b := 3;
  a_inv := 1; 
  a_inv_correct := eq_refl;
  gcd_a_26 := eq_refl
|}.

Definition encrypt_char (x : Z) : Z := ((a test_affine_key) * x + (b test_affine_key)) mod 26.
Definition decrypt_char (x : Z) : Z := ((a_inv test_affine_key) * (x - (b test_affine_key))) mod 26.

Example test_encrypt_A: encrypt_char 0 = 3.
Proof. unfold encrypt_char. simpl. reflexivity. Qed.

Example test_encrypt_B: encrypt_char 1 = 4.
Proof. unfold encrypt_char. simpl. reflexivity. Qed.

Example test_decrypt_D: decrypt_char 3 = 0.
Proof. unfold decrypt_char. simpl. reflexivity. Qed.

Example test_decrypt_E: decrypt_char 4 = 1.
Proof. unfold decrypt_char. simpl. reflexivity. Qed.
