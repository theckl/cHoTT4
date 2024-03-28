import CHoTT4.Init.Path

universe u

namespace hott

def Empty.elim {A : Type _} : Empty -> A :=
  fun h : Empty => Empty.rec h

/- not -/
def Not (A : Type u) := A → Empty

prefix:75 "¬" => hott.Not

/- inequality -/
def NEq {A : Type u} (a b : A) := Not (Eq a b)

infix:55 (priority := high) " ≠ " => NEq

def NEq.inverse {A : Type u} {a b : A} (np : a ≠ b) : b ≠ a :=
  fun q => np q⁻¹

postfix:max "⁻¹" => NEq.inverse

/- decidable -/
class inductive Decidable (P : Type u) : Type u
| isTrue  :  P → Decidable P
| isFalse : ¬P → Decidable P

abbrev DecidableEq (A : Type _) :=
  (a b : A) -> Decidable (a = b)

abbrev DecidableRel {A : Type _} (R : A -> A -> Type _) :=
  (a b : A) -> Decidable (R a b)

end hott
