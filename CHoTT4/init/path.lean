/- Ported from HoTT3 -/
import CHoTT4.init.path0

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

def transport {P : A → Type v} {x y : A} : (x = y) -> (P x) -> P y
| Eq.refl => fun u => u

notation:65 q:65 " ▸ " u => transport q u
notation:65 q:65 " ▸[" P:65 "] " u => @transport _ P _ _ q u

def ap {A : Type u} {B : Type v} (f : A → B) {x y : A} :
  (p : x = y) -> f x = f y
| Eq.refl => IdP


end hott
