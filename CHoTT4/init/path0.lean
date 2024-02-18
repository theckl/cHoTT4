/- Ported from HoTT3 -/
universe u

namespace hott

/- Path equality: delivers a type, not a Prop/Sort 0 -/

inductive Eq {A : Type u} (a : A) : A → Type u
| refl : Eq a a

infix:55 (priority := high) " = " => Eq

@[reducible] def rfl {A : Type u} {a : A} := @Eq.refl _ a

end hott
