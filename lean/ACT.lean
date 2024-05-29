import Mathlib.Data.Real.Basic
import Mathlib.Data.Bool.Basic

----- Natural Numbers

-- inductive definition
inductive Natural : Type where
| zero : Natural
| suc : Natural -> Natural

----- Addition

def Natural.add : (x y : Natural) -> Natural
| m, zero => m
| m, (suc n) => suc (add m n)

-- overloads + operator
instance : Add Natural where
  add := Natural.add

lemma Natural.add_zero (x : Natural) : x + zero = x := rfl

lemma Natural.add_suc (x y : Natural) : x + suc y = suc (x + y) := rfl

lemma Natural.zero_add : (x : Natural) -> zero + x = x
| zero => rfl
| suc n => by
  rw [add_suc]
  rw [zero_add]

lemma Natural.suc_add : (x y : Natural) -> suc x + y = suc (x + y)
| m, zero => by
  rw [add_zero, add_zero]
| m, suc n => by
  rw [add_suc, add_suc]
  rw [suc_add m n]

-- attribute [simp] Natural.add_zero Natural.add_suc Natural.zero_add Natural.suc_add

lemma Natural.add_comm : (x y : Natural) -> x + y = y + x 
| zero, y => by 
  rw [zero_add, add_zero]
| suc x, y => by
  rw [add_suc]
  rw [suc_add]
  rw [add_comm]

lemma Natural.add_assoc : (x y z : Natural) -> x + (y + z) = (x + y) + z 
| zero, y, z => by
  rw [zero_add]
  rw [zero_add]
| suc n, y, z => by
  rw [suc_add]

---- Multiplication

def Natural.mul : (x y : Natural) -> Natural
| _, zero => zero
| m, (suc n) => m + (mul m n)

-- overloads * operator
instance : Mul Natural where
  mul := Natural.mul

def Natural.one : Natural := Natural.suc Natural.zero

lemma Natural.one_suc : one = Natural.suc Natural.zero := rfl

lemma Natural.mul_zero (x : Natural) : x * zero = zero := rfl

lemma Natural.mul_one (x : Natural) : x * one = x := rfl

lemma Natural.mul_suc (x y : Natural) : x * (suc y) = x + (x * y) := rfl

lemma Natural.zero_mul : (x : Natural) -> zero * x = zero
| zero => rfl
| suc n => by
  rw [mul_suc]
  rw [zero_mul]
  rw [add_zero]

lemma Natural.one_mul : (x : Natural) -> one * x = x
| zero => by
  rw [mul_zero]
| suc n => by
  rw [mul_suc]
  rw [one_mul]
  rw [one_suc]
  rw [suc_add]
  rw [zero_add]

lemma Natural.suc_mul : (x y : Natural) -> (suc x) * y = y + (x * y)
| zero, zero => rfl
| zero, suc m => by
  rw [← one_suc]
  rw [one_mul]
  rw [zero_mul]
  rw [add_zero]
| suc n, zero => by
  rw [mul_zero, mul_zero, add_zero]
| suc n, suc m => by
  rw [mul_suc,mul_suc]
  rw [suc_add,suc_add,suc_add]
  rw [suc_mul n m, suc_mul (suc n) m, suc_mul n m]
  rw [suc_add]
  rw [add_suc]
  rw [add_assoc, add_assoc m n (m + n * m)]
  rw [add_comm m n]

-- attribute [simp] Natural.mul_zero Natural.mul_one Natural.mul_suc Natural.zero_mul Natural.one_mul Natural.suc_mul

lemma Natural.mul_comm : (x y : Natural) -> x * y = y * x 
| zero, m => by
  rw [zero_mul, mul_zero]
| suc n, m => by
  

lemma Natural.distr : (x y z : Natural) -> (x + y) * z = x * z + y * z := sorry

lemma Natural.mul_assoc : (x y z : Natural) -> x * (y * z) = (x * y) * z := sorry


lemma modus_ponens (p q : Prop) : p ∧ (p → q) → q := by
  intros h
  exact h.right h.left

lemma modus_tolens (p q : Prop) : ¬ q ∧ (p → q) → ¬ p := by
  intros h
  exact h.left q
  
