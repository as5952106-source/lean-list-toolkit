import Std

/-! Total list algorithms, with correctness checked by the Lean kernel. -/
namespace LeanWork

/-- Reverse a list onto an existing suffix. Tail recursive, with no partial cases. -/
def reverseOnto (xs acc : List α) : List α :=
  match xs with
  | [] => acc
  | x :: rest => reverseOnto rest (x :: acc)

/-- The accumulator implementation agrees with the standard specification. -/
theorem reverseOnto_eq (xs acc : List α) :
    reverseOnto xs acc = xs.reverse ++ acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => simp [reverseOnto, ih, List.reverse_cons, List.append_assoc]

/-- Reverse with an initially empty accumulator. -/
def reverse (xs : List α) : List α := reverseOnto xs []

theorem reverse_eq (xs : List α) : reverse xs = xs.reverse := by
  simp [reverse, reverseOnto_eq]

theorem reverse_length (xs : List α) : (reverse xs).length = xs.length := by
  simp [reverse_eq]

theorem reverse_involutive (xs : List α) : reverse (reverse xs) = xs := by
  simp [reverse_eq]

/-- Map once, preserving order and length. -/
def map (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: map f xs

theorem map_eq (f : α → β) (xs : List α) : map f xs = xs.map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [map, ih]

theorem map_length (f : α → β) (xs : List α) : (map f xs).length = xs.length := by
  simp [map_eq]

theorem map_reverse (f : α → β) (xs : List α) :
    map f (reverse xs) = reverse (map f xs) := by
  simp [map_eq, reverse_eq, List.map_reverse]

end LeanWork
