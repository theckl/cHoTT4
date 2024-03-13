/- Ported from HoTT3 -/
import CHoTT4.Init.Path0

universe u v

namespace hott

def IdP {A : Type u} {a : A} := @rfl _ a
def IdPath {A : Type u} (a : A) := @rfl _ a

def Eq.inverse {A : Type u} {a b : A} : (p : a = b) -> b = a
| Eq.refl => Eq.refl

postfix:max "⁻¹" => Eq.inverse

def Eq.concat {A : Type u} {a b c : A} : a = b -> b = c -> a = c
| Eq.refl => (fun q => q)

infix:75 " ⬝ " => Eq.concat

-- The right inverse law.
def con.right_inv {A : Type u} {x y : A} : (p : x = y) -> p ⬝ p⁻¹ = IdP
  | Eq.refl => Eq.refl

-- The left inverse law.
def con.left_inv {A : Type u} {x y : A} : (p : x = y) -> p⁻¹ ⬝ p = IdP
  | Eq.refl => Eq.refl

def Transport {P : A → Type v} {x y : A} : (x = y) -> (P x) -> P y
| Eq.refl => fun u => u

notation:65 q:65 " ▸ " u => Transport q u
notation:65 q:65 " ▸[" P:65 "] " u => @Transport _ P _ _ q u

def Ap {A : Type u} {B : Type v} (f : A → B) {x y : A} :
  (p : x = y) -> f x = f y
| Eq.refl => IdP

def Ap011  (f : A → B → C) : a = a' -> b = b' -> f a b = f a' b'
| Eq.refl, Eq.refl => rfl

end hott
