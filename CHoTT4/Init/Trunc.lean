import CHoTT4.Init.Path
import CHoTT4.Init.ZeroOne

universe u

namespace hott

inductive truncIndex : Type
| minusTwo : truncIndex
| succ : truncIndex → truncIndex

notation "ℕ₋₂" => truncIndex

open truncIndex

@[instance]
def hasZero_truncIndex : Zero ℕ₋₂ :=
  Zero.mk (succ (succ minusTwo))

@[instance]
def hasOne_truncIndex : One ℕ₋₂ :=
  One.mk (succ (succ (succ minusTwo)))

namespace truncIndex

notation "-1" => truncIndex.succ truncIndex.minusTwo
notation "-2" => truncIndex.minusTwo

postfix:(max+1) ".+1" => truncIndex.succ

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
  (toInternal : isTruncInternal n A)

open truncIndex

namespace isTrunc

notation "isContr" => isTrunc -2
notation "isProp"  => isTrunc -1
notation "isSet"   => isTrunc 0

def isTrunc_succ_intro {A : Type _} {n : ℕ₋₂} (_ : (x y : A) -> isTrunc n (x = y)) :
  isTrunc (truncIndex.succ n) A :=
isTrunc.mk (fun _ _ => isTrunc.toInternal)

@[instance]
def isTrunc_eq (n : ℕ₋₂) [H : isTrunc (truncIndex.succ n) A] (x y : A) :
  isTrunc n (x = y) :=
isTrunc.mk (@isTrunc.toInternal (truncIndex.succ n) A H x y)

def Center (A : Type _) [H : isContr A] : A :=
  @contrInternal.Center A (@isTrunc.toInternal -2 A H)

def CenterEq [H : isContr A] (a : A) : Center _ = a :=
  contrInternal.CenterEq (@isTrunc.toInternal -2 A H) a

def isContr.mk (Center : A) (CenterEq : ∀ (a : A), Center = a) : isContr A :=
  isTrunc.mk (contrInternal.mk Center CenterEq)

def Eq_of_isContr [isContr A] (x y : A) : x = y :=
  (CenterEq x)⁻¹ ⬝ (CenterEq y)

def PropEq_of_isContr {A : Type _} [H : isContr A] {x y : A} (p q : x = y) : p = q :=
  (K p)⁻¹ ⬝ K q where
  K : ∀ (r : x = y), Eq_of_isContr x y = r
      | Eq.refl => by apply con.left_inv

def isContrEq {A : Type _} [isContr A] (x y : A) : isContr (x = y) :=
  isContr.mk (Eq_of_isContr _ _) (fun _ => PropEq_of_isContr _ _)

/- `isTrunc` is closed upwards. -/
@[instance]
def isTrunc_succ {A : Type _} : (n : ℕ₋₂) -> [isTrunc n A] ->
   isTrunc (truncIndex.succ n) A
| minusTwo, H => by apply isTrunc_succ_intro
                    intros x y
                    exact  @isContrEq A H x y
| succ n  , H => by apply isTrunc_succ_intro
                    intros x y
                    exact @isTrunc_succ _ n (@isTrunc_eq _ n H _ _)

def isProp.elim [H : isProp A] (x y : A) : x = y := by
  apply Center

@[instance]
def isProp_of_Imp_isContr {A : Type _} (H : A → isContr A) : isProp A :=
  @isTrunc_succ_intro A -2 (fun x y => by apply @isContrEq _ (H x))

@[instance]
def isProp.mk {A : Type _} (H : ∀x y : A, x = y) : isProp A :=
  isProp_of_Imp_isContr (fun x => isContr.mk x (H x))

end isTrunc

end hott
