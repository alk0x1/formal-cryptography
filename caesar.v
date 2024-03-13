Require Import Nat Arith Ascii String.
Open Scope char_scope.

Definition char_to_num (c : ascii) : nat :=
  match c with
  | "A" => 0  | "B" => 1 | "C" => 2  	| "D" => 3  | "E" => 4
  | "F" => 5  | "G" => 6  | "H" => 7  | "I" => 8  | "J" => 9
  | "K" => 10 | "L" => 11 | "M" => 12 | "N" => 13 | "O" => 14
  | "P" => 15 | "Q" => 16 | "R" => 17 | "S" => 18 | "T" => 19
  | "U" => 20 | "V" => 21 | "W" => 22 | "X" => 23 | "Y" => 24
  | "Z" => 25
  | _ => 0
  end.

Definition num_to_char (n : nat) : ascii :=
  match n with
  | 0 => "A" | 1 => "B" | 2 => "C" | 3 => "D" | 4 => "E"
  | 5 => "F" | 6 => "G" | 7 => "H" | 8 => "I" | 9 => "J"
  | 10 => "K" | 11 => "L" | 12 => "M" | 13 => "N" | 14 => "O"
  | 15 => "P" | 16 => "Q" | 17 => "R" | 18 => "S" | 19 => "T"
  | 20 => "U" | 21 => "V" | 22 => "W" | 23 => "X" | 24 => "Y"
  | 25 => "Z"
  | _ => "A"
  end.

Definition letter := nat.

Definition letter_to_ascii (l : letter) : ascii :=
  match l with
  | 0 => "A"
  | 1 => "B"
  | 2 => "C"
  | 3 => "D"
  | 4 => "E"
  | 5 => "F"
  | 6 => "G"
  | 7 => "H"
  | 8 => "I"
  | 9 => "J"
  | 10 => "K"
  | 11 => "L"
  | 12 => "M"
  | 13 => "N"
  | 14 => "O"
  | 15 => "P"
  | 16 => "Q"
  | 17 => "R"
  | 18 => "S"
  | 19 => "T"
  | 20 => "U"
  | 21 => "V"
  | 22 => "W"
  | 23 => "X"
  | 24 => "Y"
  | 25 => "Z"
  | _ => "?"
  end.

Definition ascii_to_letter (a : ascii) : letter :=
  let n := nat_of_ascii a in
  if andb (Nat.leb 65 n) (Nat.leb n 90) then n - 65  (* 'A' to 'Z' *)
  else if andb (Nat.leb 97 n) (Nat.leb n 122) then n - 97  (* 'a' to 'z' *)
  else 0. (* Fallback case for non-letter inputs *)

Definition mod26 (n : nat) : nat := n mod 26.

Definition shift (n shift_val : nat) : nat := mod26 (n + shift_val).
Definition encrypt_shift := 3.
Definition decrypt_shift := 26 - encrypt_shift.

Definition encrypt_char (l : letter) : letter := shift l encrypt_shift.
Definition decrypt_char (l : letter) : letter := shift l decrypt_shift.

Example test_decrypt_D: decrypt_char 3 = 0.
Proof. simpl. reflexivity. Qed.


Fixpoint encrypt_string (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => let l := ascii_to_letter c in
    let enc_c := letter_to_ascii (encrypt_char l) in
    String enc_c (encrypt_string s')
  end.

Compute (encrypt_string "ABC").

Fixpoint decrypt_string (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => let l := ascii_to_letter c in
    let enc_c := letter_to_ascii (decrypt_char l) in
    String enc_c (decrypt_string s')
  end.
 
Compute (decrypt_string "DEF").


Example test_encrypt_str: encrypt_string "ABC" = "DEF"%string.

Example test_encrypt_A: encrypt_char 0 = 3.
Proof. simpl. reflexivity. Qed.
 
Example test_decrypt_A: decrypt_char 3 = 0.
Proof. reflexivity. Qed.

