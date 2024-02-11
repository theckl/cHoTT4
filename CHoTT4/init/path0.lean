/- Ported from HoTT3 -/
universe u

namespace hott

/- Path equality: delivers a type, not a Prop/Sort 0 -/

inductive eq {A : Type u} (a : A) : A → Type u
| refl : eq a a

local infix:55 " = " => hott.eq

@[reducible] def rfl {A : Type u} {a : A} := @eq.refl _ a

end hott
