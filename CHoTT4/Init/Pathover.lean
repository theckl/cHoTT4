  /- Ported from HoTT3 -/
import CHoTT4.Init.Path

universe u v

namespace hott

inductive Pathover {A : Type u} (B : A → Type u) :
  {a : A} -> (b : B a) -> {a₂ : A} -> (b₂ : B a₂) -> a = a₂ → Type u
| idpatho : Pathover B b b rfl

notation b:50 " =[" p:0 "] " b₂:50 => Pathover _ b b₂ p
notation b:50 " =[" p:0 "; " B "] " b₂:50 => Pathover B b b₂ p

@[reducible]
def IdPo : b =[Eq.refl] b :=
  Pathover.idpatho

def PathoverOfTrEq {A : Type _} {B : A → Type _} {a : A} {a₂ : A} :
  (p : a = a₂) -> {b : B a} -> {b₂ : B a₂} -> (r : (p ▸ b) = b₂) -> b =[p] b₂
| Eq.refl, _, _, Eq.refl => IdPo

def ApD011 {A C : Type _} {B : A -> Type _} (f : (a : A) → B a → C) {a a' : A} :
  (p : a = a') -> {b : B a} -> {b' : B a'} -> (q : b =[p] b') -> f a b = f a' b'
| Eq.refl, _, _, Pathover.idpatho => rfl

end hott
