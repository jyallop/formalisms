
inductive ℕ : Type 
| z : ℕ
| suc : ℕ → ℕ

def add : ℕ → ℕ → ℕ
| z, n => n
| (suc m), n => add m (suc n)

