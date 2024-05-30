
inductive Integer where
| zero : Integer
| succ : Integer → Integer

def add : Integer → Integer → Integer
| Integer.zero, y => y
| (Integer.succ n), y => add n (Integer.succ y)

