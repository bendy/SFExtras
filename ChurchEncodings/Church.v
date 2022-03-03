(* (Deeply Embedded) Church Encoded Datatypes in Coq. *)

(** Our job for this lab: Demo church encoded datatypes using our
    formalization of the untyped lambda calculus.
    *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From PLF Require Import Maps.
From PLF Require Import Smallstep.
From Church Require Import LCNat.

(* Defining some helpful variable identifiers. *)
Definition c : string := "c".
Definition n : string := "n".
Definition l : string := "l".
Definition hd : string := "hd".
Definition tl : string := "tl".


(* Church Encodings: *)
(* We can actually encode booleans in the pure lambda calculus. We
   will define true and false as follows: *)

Definition true_church := <{\t, \f, t}>.
Definition false_church := <{\t, \f, f}>.

(* These terms encode booleans, in the sense that we can use these
   terms to mimic the behavior of conditionals in the pure lambda
   calculus. In particular, we can encode an if expression as follows:
   *)

Definition if_church := <{\x, \t, \f, x t f}>.
(* This term doesn't do much: it just applies the conditional to the
   two branches: if it is [true_church], it evaluates to the first
   expression, and [false_church] evaluates to the second. *)

Example if_true :
  <{if_church true_church (S tm_zero) tm_zero}> -->* <{S tm_zero}>.
Proof.
  normalize_lambda.
  apply multi_refl.
Qed.

Example if_false :
  <{if_church false_church (S tm_zero) tm_zero}> -->* <{tm_zero}>.
Proof.
  normalize_lambda.
  apply multi_refl.
Qed.

(* We can define boolean operations like and as well! *)
Definition and_church :=
  <{\x, \y, x y false_church}>.

Example if_and_false :
  <{if_church (and_church true_church false_church) (S tm_zero) tm_zero}> -->* <{tm_zero}>.
Proof.
  normalize_lambda.
  apply multi_refl.
Qed.

(* We can encode pairs as terms using booleans: *)
Definition pair_church :=
  <{\f, \s, \x, x f s}>.

Definition fst_church :=
  <{\y, y true_church}>.

Definition snd_church :=
  <{\y, y false_church}>.

(* That is, [pair f s] is a function, that when applied to a boolean
   [x], applies [x] to [f] and [s]. By definition, this function
   returns [f] when [x] is [true_church] and [s] when [x] is
   [false_church]. The standard projection functions just supply the
   appropriate church-encoded boolean. *)

Example fst_pair :
  <{fst_church (pair_church (S tm_zero) tm_zero)}> -->* <{S tm_zero}>.
Proof.
  normalize_lambda.
  apply multi_refl.
Qed.

(* Interestingly, we can encode numbers using a similar technique.
   The key difference is that we need to handle recursion more
   delicately.

   Informally, we can define church-encoded numbers as follows:

   C0 = \s, \z, z
   C1 = \s, \z, s z
   C2 = \s, \z, s (s z)
   C3 = \s, \z, s (s (s z))
 *)

(* That is, a number takes two functions: one for the successor case,
   and one for the zero case.  The key bit is that the function for
   what to do in the successor case takes an argument for the result
   of its predecessor. The 'number' simply recursively applies the
   successor function the appropriate number of times. *)

(* As examples, here are the church encoding of zero and three: *)

Definition zero_church :=
  <{\s, \z, z}>.

Definition three_church :=
  <{\s, \z, s (s (s z))}>.

(* If we supply tm_succ for the recursive case, and tm_zero for the
   base case, we can convert this number to the primitive numbers. *)
Example three_church_ex :
  <{three_church (\z, S z) tm_zero}> -->* <{S (S (S tm_zero)) }>.
Proof.
  normalize_lambda.
  apply multi_refl.
Qed.

(* We can define a generalized successor function, which takes a
   church number and yields another church number: *)
Definition succ_church :=
  <{\x, \s, \z, s (x s z)}>.

Definition one_church :=
  <{succ_church zero_church}>.

Definition two_church :=
  <{succ_church (succ_church zero_church)}>.

Example church_ex_1 :
  <{zero_church (\z, S z) tm_zero}> -->* <{tm_zero }>.
Proof.
  normalize_lambda.
  apply multi_refl.
Qed.

Example church_ex_2 :
  <{(succ_church zero_church) (\z, S z) tm_zero}> -->* <{S tm_zero }>.
Proof.
  normalize_lambda.
  apply multi_refl.
Qed.

(* We can also define addition on church encoded numerals: *)
Definition plus_church :=
  <{\x, \y, \s, \z, x s (y s z)}>.

Example plus_ex_1 :
  <{(plus_church (succ_church zero_church) zero_church) (\z, S z) tm_zero}> -->* <{S tm_zero }>.
Proof.
  normalize_lambda.
  apply multi_refl.
Qed.

(* Testing if a number is zero is straightforward: *)
Definition is_zero_church :=
  <{\x, x (\y, false_church) true_church}>.
(* It returns true in the base (zero) case, and throws away the
   recursive result in the second case to simply return false.*)
Example is_zero_ex :
  <{is_zero_church (succ_church zero_church)}> -->* <{false_church}>.
Proof.
  normalize_lambda.
  apply multi_refl.
Qed.

(* Finally, for good measure, here are the church encoding of nil and
   cons (for lists of natural numbers): *)

Definition nil_church :=
  <{\c, \n, n}>.

Definition cons_church :=
  <{\hd, \tl, \c, \n, c hd (tl c n)}>.

(* The list [1; 2]*)
Definition one_two_church :=
  <{cons_church one_church (cons_church two_church nil_church)}>.

(* IsNil for church-encoded lists:
   λl. l (λt f. t) (λt f. f)          *)

Definition isnil_church :=
  <{\l, l (\x, \y, false_church) true_church}>.

Example isnil_ex :
  <{ isnil_church nil_church }> -->* <{true_church}>.
Proof.
  normalize_lambda.
  apply multi_refl.
Qed.

Example isnil_ex_2 :
  <{ isnil_church one_two_church }> -->* <{false_church}>.
Proof.
  normalize_lambda.
  apply multi_refl.
Qed.

(* Length of a church-encoded list:
   λl. l (λhd n. λz s. s (n z s)) (λz. λs. z) *)

Definition length_church :=
  <{\l, l (\x, succ_church) zero_church }>.

Example length_ex :
  <{ (length_church nil_church) (\z, S z) tm_zero}> -->* <{tm_zero}>.
Proof.
  normalize_lambda.
  apply multi_refl.
Qed.

Example length_ex_2 :
  <{ (length_church one_two_church) (\z, S z) tm_zero}> -->* <{S (S tm_zero)}>.
Proof.
  normalize_lambda.
  apply multi_refl.
Qed.

Example length_ex_3 :
  <{ (length_church (cons_church three_church one_two_church)) (\z, S z) tm_zero}> -->* <{S (S (S tm_zero))}>.
Proof.
  normalize_lambda.
  apply multi_refl.
Qed.

(* Summing the elements of a church-encoded list of numbers:
   λl. l (λz. λs. z) (λhd n. λz s. plus hd (n z s)) *)

Definition sum_church :=
  <{\l, l (\hd, \tl, plus_church hd tl) zero_church }>.

Example sum_ex :
  <{ (sum_church nil_church) (\z, S z) tm_zero}> -->* <{tm_zero}>.
Proof.
  normalize_lambda.
  apply multi_refl.
Qed.

Example sum_ex_2 :
  <{ (sum_church one_two_church) (\z, S z) tm_zero}> -->* <{S (S (S tm_zero))}>.
Proof.
  normalize_lambda.
  apply multi_refl.
Qed.

(* Surprisingly, the predecessor function is quite tricky to
   define. This is because Church encodings are destructive: they
   always "process" subdata by applying the recursive call. Thus, we
   can't access any of the recursive subdata of a constructor, only
   the 'result' of recursively processing that function. *)

Definition pred_church :=
  <{\x, fst_church (x (\y, pair_church (snd_church y)
                                       (succ_church (snd_church y)))
                      (pair_church zero_church zero_church)) }>.

(* The definition works by using [x] to apply [x] copies of a function
   that takes a pair [(c1, c2)] and produces a pair [(c2, 1 + c2)].
   applying this function x times to the pair [(0, 0)] results in the
   pair [(x - 1, x)]. Throwing away the second argument yields the
   predecessor of x.  *)

Example pred_ex :
  <{ pred_church three_church (\z, S z) tm_zero }> -->* <{S (S tm_zero)}>.
Proof.
  normalize_lambda.
  apply multi_refl.
Qed.
