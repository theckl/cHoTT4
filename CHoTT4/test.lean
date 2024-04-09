inductive vectorI {A : Type} (n : Nat) : Type where
| nil : vectorI n

#check System.FilePath.pathExists

def woodlandCritters : List String :=
  ["hedgehog", "deer", "snail"]

def hedgehog := woodlandCritters[0]
def deer := woodlandCritters[1]
def snail := woodlandCritters[2]

structure Pos where
  succ ::
  pred : Nat

def Pos.plus : Pos -> Pos -> Pos
| succ p, succ q => succ (p + q + 1)

instance : Add Pos where
  add := Pos.plus

def Pos.mul : Pos -> Pos -> Pos
| succ p, succ q => succ (p * q + p + q)

instance : Mul Pos where
  mul := Pos.mul

def Pos.toNat : Pos -> Nat
| succ p => p + 1

instance : ToString Pos where
  toString x := toString (x.toNat)

def seven : Pos := Pos.succ 6

def fourteen : Pos := seven + seven

#eval fourteen

instance : OfNat Pos (n + 1) where
  ofNat := Pos.succ n

def eight : Pos := 8

structure Even where
  double ::
  half : Nat

def Even.plus : Even -> Even -> Even
| double p, double q => double (p + q)

instance : Add Even where
  add := Even.plus

def Even.mul : Even -> Even -> Even
| double p, double q => double (2 * p * q)

instance : Mul Even where
  mul := Even.mul

def Even.toNat : Even -> Nat
| double p => 2 * p

instance : ToString Even where
  toString x := toString (x.toNat)

def six : Even := Even.double 3

def twelve : Even := six + six

#eval twelve

instance : OfNat Even 0 where
  ofNat := Even.double 0

instance Even.OfNat_step {n : Nat} [OfNat Even n] : OfNat Even (n + 2) where
  ofNat := Even.double (Even.half (OfNat.ofNat n) + 1)

def ten : Even := 10

#eval ten
