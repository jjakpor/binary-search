import BinarySearch.Basic

-- Examples of searching an array.
section Example
def arr : List ℕ := [1, 3, 4, 6, 9]
def p : ℕ → Bool := searchPred arr 5
#eval binarySearch p searchMid (0, 6)

variable (ι : Type) [LinearOrder ι]
variable (pred : ι → Bool)
abbrev Pair' := ι × ι

def searchStep' (pair : Pair' ι) (m : ι): Pair' ι :=
  if pred m
    then (pair.fst, m)
    else (m, pair.snd)
variable (mid' : (p : Pair' ι) → Option ι)

/- This is partial because termination was proven for pairs of Nats, not ιs.
   The logic should be similar.
-/
partial def binarySearch' (pair : Pair' ι) : Pair' ι :=
  match mid' pair with
  | none => pair
  | some m =>
    binarySearch' (searchStep' ι pred pair m)

/- Finding the square root of floating point numbers. -/
def floatMid (ε : Float) (p : Pair' Float) : Option Float :=
  if p.snd - p.fst > ε then some (p.fst + (p.snd - p.fst) / 2) else none
def floatPred (target : Float) (x : Float) : Bool := x * x > target

#eval binarySearch' Float (floatPred 2.0) (floatMid 0.00001) (1, 2)
end Example
