def FermatLastTheorem :=
  ∀ x y z n : Nat, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

theorem blah : ∀ x : Nat, x = x :=  
  by
    intros x
    rfl

theorem hello (x : Nat) : Nat :=
  x

def cool (x y : Nat) (h : x = y) : x = y :=
    h
