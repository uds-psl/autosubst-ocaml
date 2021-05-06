(* adding another argument about doubles the time
 adding another mutual recursive entry is much worse *)

(* | Arguments \ mutual inductives |   6 |    7 | *)
(* |-------------------------------+-----+------| *)
(* |                             6 | 1.4 | 11.0 | *)
(* |                             7 | 3.4 | 35.4 | *)
(* |                             8 | 7.3 | 80.3 | *)

(* Fixpoint foo0 (m n: nat) {struct m} := *)
(*   match m with *)
(*   | O => true *)
(*   | S m0 => foo1 m0 n *)
(*   end *)
(* with foo1 (m n: nat) {struct n} := *)
(*      match n with *)
(*      | O => true *)
(*      | S n => foo1 m n *)
(*      end. *)

Module m1.
  (* 6 fixpoints with 6 arguments each. Last one is structural *)
  (* takes 1.4 seconds *)
  Time Fixpoint foo0 {n0 n1 n2 n3 n4} (H: n0 + n1 + n2 + n3 + n4 = 0) (n: nat) :=
    match n with
    | O => true
    | S n => foo1 H n
    end
  with foo1 {n0 n1 n2 n3 n4} (H: n0 + n1 + n2 + n3 + n4 = 0) (n: nat) :=
         match n with
         | O => true
         | S n => foo2 H n
         end
  with foo2 {n0 n1 n2 n3 n4} (H: n0 + n1 + n2 + n3 + n4 = 0) (n: nat) :=
         match n with
         | O => true
         | S n => foo3 H n
         end
  with foo3 {n0 n1 n2 n3 n4} (H: n0 + n1 + n2 + n3 + n4 = 0) (n: nat) :=
         match n with
         | O => true
         | S n => foo4 H n
         end
  with foo4 {n0 n1 n2 n3 n4} (H: n0 + n1 + n2 + n3 + n4 = 0) (n: nat) :=
         match n with
         | O => true
         | S n => foo5 H n
         end
  with foo5 {n0 n1 n2 n3 n4} (H: n0 + n1 + n2 + n3 + n4 = 0) (n: nat) :=
         match n with
         | O => true
         | S n => foo0 H n
         end.
End m1.

Module m2.
  (* 6 fixpoints with 7 arguments each. Last one is structural *)
  (* takes 3.4 seconds *)
  Time Fixpoint foo0 {n0 n1 n2 n3 n4 n5} (H: n0 + n1 + n2 + n3 + n4 + n5 = 0) (n: nat) :=
    match n with
    | O => true
    | S n => foo1 H n
    end
  with foo1 {n0 n1 n2 n3 n4 n5} (H: n0 + n1 + n2 + n3 + n4 + n5 = 0) (n: nat) :=
      match n with
      | O => true
      | S n => foo2 H n
         end
  with foo2 {n0 n1 n2 n3 n4 n5} (H: n0 + n1 + n2 + n3 + n4 + n5 = 0) (n: nat) :=
         match n with
         | O => true
         | S n => foo3 H n
         end
  with foo3 {n0 n1 n2 n3 n4 n5} (H: n0 + n1 + n2 + n3 + n4 + n5 = 0) (n: nat) :=
         match n with
         | O => true
         | S n => foo4 H n
         end
  with foo4 {n0 n1 n2 n3 n4 n5} (H: n0 + n1 + n2 + n3 + n4 + n5 = 0) (n: nat) :=
         match n with
         | O => true
         | S n => foo5 H n
         end
  with foo5 {n0 n1 n2 n3 n4 n5} (H: n0 + n1 + n2 + n3 + n4 + n5 = 0) (n: nat) :=
         match n with
         | O => true
         | S n => foo0 H n
         end.
End m2.

Module m3.
  (* 6 fixpoints with 8 arguments each. Last one is structural *)
  (* takes 7.3 seconds *)
  Time Fixpoint foo0 {n0 n1 n2 n3 n4 n5 n6} (H: n0 + n1 + n2 + n3 + n4 + n5 + n6 = 0) (n: nat) :=
    match n with
    | O => true
    | S n => foo1 H n
    end
  with foo1 {n0 n1 n2 n3 n4 n5 n6} (H: n0 + n1 + n2 + n3 + n4 + n5 + n6 = 0) (n: nat) :=
      match n with
      | O => true
      | S n => foo2 H n
         end
  with foo2 {n0 n1 n2 n3 n4 n5 n6} (H: n0 + n1 + n2 + n3 + n4 + n5 + n6 = 0) (n: nat) :=
         match n with
         | O => true
         | S n => foo3 H n
         end
  with foo3 {n0 n1 n2 n3 n4 n5 n6} (H: n0 + n1 + n2 + n3 + n4 + n5 + n6 = 0) (n: nat) :=
         match n with
         | O => true
         | S n => foo4 H n
         end
  with foo4 {n0 n1 n2 n3 n4 n5 n6} (H: n0 + n1 + n2 + n3 + n4 + n5 + n6 = 0) (n: nat) :=
         match n with
         | O => true
         | S n => foo5 H n
         end
  with foo5 {n0 n1 n2 n3 n4 n5 n6} (H: n0 + n1 + n2 + n3 + n4 + n5 + n6 = 0) (n: nat) :=
         match n with
         | O => true
         | S n => foo0 H n
         end.
End m3.

Module m4.
  (* 7 fixpoints with 6 arguments each. Last one is structural *)
  (* takes 11.0 seconds *)
  Time Fixpoint foo0 {n0 n1 n2 n3 n4} (H: n0 + n1 + n2 + n3 + n4 = 0) (n: nat) :=
    match n with
    | O => true
    | S n => foo1 H n
    end
  with foo1 {n0 n1 n2 n3 n4} (H: n0 + n1 + n2 + n3 + n4 = 0) (n: nat) :=
         match n with
         | O => true
         | S n => foo2 H n
         end
  with foo2 {n0 n1 n2 n3 n4} (H: n0 + n1 + n2 + n3 + n4 = 0) (n: nat) :=
         match n with
         | O => true
         | S n => foo3 H n
         end
  with foo3 {n0 n1 n2 n3 n4} (H: n0 + n1 + n2 + n3 + n4 = 0) (n: nat) :=
         match n with
         | O => true
         | S n => foo4 H n
         end
  with foo4 {n0 n1 n2 n3 n4} (H: n0 + n1 + n2 + n3 + n4 = 0) (n: nat) :=
         match n with
         | O => true
         | S n => foo5 H n
         end
  with foo5 {n0 n1 n2 n3 n4} (H: n0 + n1 + n2 + n3 + n4 = 0) (n: nat) :=
         match n with
         | O => true
         | S n => foo6 H n
         end
  with foo6 {n0 n1 n2 n3 n4} (H: n0 + n1 + n2 + n3 + n4 = 0) (n: nat) :=
         match n with
         | O => true
         | S n => foo0 H n
         end.
End m4.

Module m5.
  (* 7 fixpoints with 7 arguments each. Last one is structural *)
  (* takes 35.4 seconds *)
  Time Fixpoint foo0 {n0 n1 n2 n3 n4 n5} (H: n0 + n1 + n2 + n3 + n4 + n5 = 0) (n: nat) :=
    match n with
    | O => true
    | S n => foo1 H n
    end
  with foo1 {n0 n1 n2 n3 n4 n5} (H: n0 + n1 + n2 + n3 + n4 + n5 = 0) (n: nat) :=
      match n with
      | O => true
      | S n => foo2 H n
         end
  with foo2 {n0 n1 n2 n3 n4 n5} (H: n0 + n1 + n2 + n3 + n4 + n5 = 0) (n: nat) :=
         match n with
         | O => true
         | S n => foo3 H n
         end
  with foo3 {n0 n1 n2 n3 n4 n5} (H: n0 + n1 + n2 + n3 + n4 + n5 = 0) (n: nat) :=
         match n with
         | O => true
         | S n => foo4 H n
         end
  with foo4 {n0 n1 n2 n3 n4 n5} (H: n0 + n1 + n2 + n3 + n4 + n5 = 0) (n: nat) :=
         match n with
         | O => true
         | S n => foo5 H n
         end
  with foo5 {n0 n1 n2 n3 n4 n5} (H: n0 + n1 + n2 + n3 + n4 + n5 = 0) (n: nat) :=
         match n with
         | O => true
         | S n => foo6 H n
         end
  with foo6 {n0 n1 n2 n3 n4 n5} (H: n0 + n1 + n2 + n3 + n4 + n5 = 0) (n: nat) :=
         match n with
         | O => true
         | S n => foo0 H n
         end.
End m5.

Module m6.
  (* 7 fixpoints with 8 arguments each. Last one is structural *)
  (* takes 80.3 seconds *)
  Time Fixpoint foo0 {n0 n1 n2 n3 n4 n5 n6} (H: n0 + n1 + n2 + n3 + n4 + n5 + n6 = 0) (n: nat) :=
    match n with
    | O => true
    | S n => foo1 H n
    end
  with foo1 {n0 n1 n2 n3 n4 n5 n6} (H: n0 + n1 + n2 + n3 + n4 + n5 + n6 = 0) (n: nat) :=
      match n with
      | O => true
      | S n => foo2 H n
         end
  with foo2 {n0 n1 n2 n3 n4 n5 n6} (H: n0 + n1 + n2 + n3 + n4 + n5 + n6 = 0) (n: nat) :=
         match n with
         | O => true
         | S n => foo3 H n
         end
  with foo3 {n0 n1 n2 n3 n4 n5 n6} (H: n0 + n1 + n2 + n3 + n4 + n5 + n6 = 0) (n: nat) :=
         match n with
         | O => true
         | S n => foo4 H n
         end
  with foo4 {n0 n1 n2 n3 n4 n5 n6} (H: n0 + n1 + n2 + n3 + n4 + n5 + n6 = 0) (n: nat) :=
         match n with
         | O => true
         | S n => foo5 H n
         end
  with foo5 {n0 n1 n2 n3 n4 n5 n6} (H: n0 + n1 + n2 + n3 + n4 + n5 + n6 = 0) (n: nat) :=
         match n with
         | O => true
         | S n => foo6 H n
         end
  with foo6 {n0 n1 n2 n3 n4 n5 n6} (H: n0 + n1 + n2 + n3 + n4 + n5 + n6 = 0) (n: nat) :=
         match n with
         | O => true
         | S n => foo0 H n
         end.
End m6.

