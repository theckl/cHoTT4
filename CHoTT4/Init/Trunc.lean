import CHoTT4.Init.Path
import CHoTT4.Init.ZeroOne

universe u

namespace hott

inductive truncIndex : Type
| minusTwo : truncIndex
| Succ : truncIndex → truncIndex

notation "ℕ₋₂" => truncIndex

open truncIndex

@[instance]
def hasZero_truncIndex : Zero ℕ₋₂ :=
  Zero.mk (Succ (Succ minusTwo))

@[instance]
def hasOne_truncIndex : One ℕ₋₂ :=
  One.mk (Succ (Succ (Succ minusTwo)))

namespace truncIndex

notation "-1" => truncIndex.Succ truncIndex.minusTwo
notation "-2" => truncIndex.minusTwo

end truncIndex

open truncIndex
namespace isTrunc

structure contrInternal (A : Type u) :=
    (Center : A)
    (CenterEq : (a : A) -> Center = a)

def isTruncInternal (n : ℕ₋₂) : Type u → Type u :=
    truncIndex.recOn n (fun A => contrInternal A)
                       (fun _ trunc_n A => ((x y : A) -> trunc_n (x = y)))

end isTrunc

open isTrunc

class isTrunc (n : ℕ₋₂) (A : Type u) :=
  (to_internal : isTruncInternal n A)

open truncIndex

namespace isTrunc

notation "is_contr" => isTrunc -2
notation "is_prop"  => isTrunc -1
notation "is_set"   => isTrunc 0

end isTrunc

end hott
