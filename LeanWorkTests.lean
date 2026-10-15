import LeanWork

example : LeanWork.reverse ([] : List Nat) = [] := rfl
example : LeanWork.reverse [1, 2, 3, 4] = [4, 3, 2, 1] := rfl
example : LeanWork.reverseOnto [1, 2] [9, 10] = [2, 1, 9, 10] := rfl
example : LeanWork.map (fun n : Nat => n + 1) [0, 1, 2] = [1, 2, 3] := rfl
example (xs : List Nat) : LeanWork.reverse (LeanWork.reverse xs) = xs :=
  LeanWork.reverse_involutive xs
example (xs : List Nat) : (LeanWork.map Nat.succ xs).length = xs.length :=
  LeanWork.map_length Nat.succ xs
