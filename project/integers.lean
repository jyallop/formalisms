
inductive Natural where
| zero : Natural
| succ : Natural → Natural

open Natural
instance : OfNat Natural 0 where
  ofNat := zero

instance : OfNat Natural (n + 1) where
  ofNat :=
    let rec natPlusOne : Nat → Natural
      | 0 => zero
      | k + 1 => succ (natPlusOne k)
    natPlusOne n

def add : Natural → Natural → Natural
| Natural.zero, y => y
| (Natural.succ n), y => add n (Natural.succ y)

instance : Add Natural where
  add := add

def mul : Natural → Natural → Natural
| zero, _ => zero
| succ zero, m => m
| succ n, m => m + (mul n m)

instance : Mul Natural where
  mul := mul

def pow : Natural → Natural → Natural
| _, zero => 1
| x, succ n => x * (pow x n)

instance : HPow Natural Natural Natural where
  hPow := pow

def div : Natural → Natural → Natural
| x, 1 => x
| x, n => x

instance : HDiv Natural Natural Natural where
  hDiv := div
--lemma Natural.add_zero (x : Natural) : x + 0 = x := sorry

def series : Natural → Natural
| zero => zero
| n@(succ m) => (n ^ (2 : Natural)) + (series m)

theorem limit_one : (n : Natural) → (series n) = n * (n + 1) * (2 * n + 1) / 6 := sorry
