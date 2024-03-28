import CHoTT4.Init.Logic
import CHoTT4.Algebra.Order

universe u

namespace hott

open Nat Algebra

attribute [-instance] instLENat
attribute [-instance] instLTNat

namespace Nat

/- Equality between natural numbers is decidable. -/
protected def Code : Nat -> Nat -> Type
| 0     , 0      => Unit
| 0     , succ _ => Empty
| succ _, 0      => Empty
| succ n, succ m => Nat.Code n m

protected def RCode : (n : Nat) -> Nat.Code n n
| 0      => Unit.unit
| succ n => Nat.RCode n

protected def Nat.encodeDir {n m : Nat} : n = m -> Nat.Code n m
| Eq.refl => Nat.RCode n

@[instance]
def Nat_has_DecidableEq : DecidableEq Nat
| 0     , 0      => Decidable.isTrue rfl
| 0     , succ _ => Decidable.isFalse (fun p => Nat.encodeDir p)
| succ _, 0      => Decidable.isFalse (fun p => Nat.encodeDir p)
| succ n, succ m => match Nat_has_DecidableEq n m with
  | Decidable.isTrue p   => Decidable.isTrue (Ap succ p)
  | Decidable.isFalse np => Decidable.isFalse (fun p => np (Ap Nat.pred p))

def succ_ne_zero : ∀ (n : Nat), ¬(succ n = 0) :=
  fun _ => Nat.encodeDir

/- order on natural numbers as a type -/
inductive Le (n : Nat) : Nat → Type
| refl : Le n n
| step : {m : Nat} -> Le n m -> Le n (Nat.succ m)

--attribute [-instance] instLENat

instance (priority := high) Nat_hasLe : hasLe Nat := hasLe.mk Nat.Le

def Lt (n m : Nat) := Nat.Le (Nat.succ n) m

--attribute [-instance] instLTNat

instance (priority := high) Dir_hasLt : hasLt Nat := hasLt.mk Lt

/- transitivity of `≤` -/
protected def LeTrans {n m l : Nat} (p : n ≤ m) : (m ≤ l) -> n ≤ l
| Le.refl => p
| @Le.step m _ q => Le.step (Nat.LeTrans p q)

def succLesucc {n m : Nat} : (n ≤ m) -> succ n ≤ succ m
| Le.refl => Le.refl
| Le.step p => Le.step (succLesucc p)

def PredLePred {n m : Nat} : succ n ≤ succ m -> (n ≤ m)
| Le.refl   => Le.refl
| Le.step p => Nat.LeTrans (Le.step (Le.refl)) p

def PredLtPred {n m : Nat} : succ n < succ m -> (n < m)
| Le.refl   => Le.refl
| Le.step p => Nat.LeTrans (Le.step (Le.refl)) p

def succ_Le_not_Zero {n m : Nat} : (p : n + 1 ≤ m) -> ¬(m = 0)
| Le.refl   => succ_ne_zero n
| Le.step p => succ_ne_zero _

def not_succ_Le_self : (n : Nat) -> ¬(succ n ≤ n)
| 0   => fun p => Empty.elim (succ_Le_not_Zero p IdP)
| n+1 => fun p => not_succ_Le_self n (PredLePred p)

protected def Lt_irrefl (n : Nat) : ¬(n < n) := not_succ_Le_self n

protected def notLtZero {n : Nat} : ¬(n < 0) := fun p => match n with
                                                    | 0 => Nat.Lt_irrefl _ p

def Le_LtorEq {n m : Nat} : n ≤ m -> n < m ⊕ n = m
| Le.refl => Sum.inr IdP
| Le.step p => Sum.inl (succLesucc p)

protected def WellFounded.recAux {C : Nat -> Type _}
  (ih : forall n : Nat, (forall m : Nat, m < n -> C m) -> C n) :
                            forall n : Nat, (forall m : Nat, m < n -> C m)
| 0      => fun _ p => Empty.elim (Nat.notLtZero p)
| succ n => fun m p => match Le_LtorEq p with
                       | Sum.inl p => WellFounded.recAux ih n m (PredLtPred p)
                       | Sum.inr p => (Ap pred p)⁻¹ ▸[C] ih n (WellFounded.recAux ih n)

protected def WellFounded.rec {C : Nat -> Type _} :
  (forall n : Nat, (forall m : Nat, m < n -> C m) -> C n) -> forall n : Nat, C n :=
fun ih n => WellFounded.recAux ih (n+1) n Le.refl

end Nat

end hott
