import CHoTT4.Types.Nat

universe u

namespace hott

attribute [-instance] instLENat
attribute [-instance] instLTNat

namespace List

/- split a list into two list of almost equal length -/
def split {A : Type _} : List A -> List A × List A
| []          => ⟨[], []⟩
| a :: l => let lp := split l
            ⟨a :: lp.2, lp.1⟩

def length_split_le {A : Type _} : (l l₁ l₂ : List A) -> (h : split l = ⟨l₁, l₂⟩) ->
  (List.length l₁ ≤ List.length l) × (List.length l₂ ≤ List.length l)
| []    , _ , _  => fun h => ⟨((Ap Prod.fst h) ▸[fun l => List.length l ≤ 0] Nat.Le.refl),
                              ((Ap Prod.snd h) ▸[fun l => List.length l ≤ 0] Nat.Le.refl)⟩
| c :: l, l₁, l₂ => fun h => by
    let lp := split l
    have e : split (c :: l) = ⟨c :: lp.2, lp.1⟩ := rfl
    have f : split l = ⟨lp.1, lp.2⟩ := rfl
    have h₁ : c :: lp.2 = l₁ := Ap Prod.fst (e⁻¹ ⬝ h)
    have h₂ : lp.1 = l₂ := Ap Prod.snd (e⁻¹ ⬝ h)
    apply Prod.mk
    . exact h₁ ▸[fun m => List.length m ≤ List.length (c :: l)]
                (Nat.succLesucc (length_split_le l lp.1 lp.2 f).2)
    . exact h₂ ▸[fun m => List.length m ≤ List.length (c :: l)]
                Nat.LeTrans (length_split_le l lp.1 lp.2 f).1 (Nat.Le.step Nat.Le.refl)

def length_split_lt {A : Type _} {a b : A} {l l₁ l₂ : List A}
  (h : split (a :: b :: l) = ⟨l₁, l₂⟩) :
  (List.length l₁ < List.length l + 2) × (List.length l₂ < List.length l + 2) := by
    let lp := split l
    have e : split (a :: b :: l) = ⟨a :: lp.1, b :: lp.2⟩ := rfl
    have f : split l = ⟨lp.1, lp.2⟩ := rfl
    have h₁ : a :: lp.1 = l₁ := Ap Prod.fst (e⁻¹ ⬝ h)
    have h₂ : b :: lp.2 = l₂ := Ap Prod.snd (e⁻¹ ⬝ h)
    apply Prod.mk
    . exact h₁ ▸[fun m => List.length m < List.length l+2]
              Nat.succLesucc (Nat.succLesucc (length_split_le l lp.1 lp.2 f).1)
    . exact h₂ ▸[fun m => List.length m < List.length l+2]
              Nat.succLesucc (Nat.succLesucc (length_split_le l lp.1 lp.2 f).2)

/- Well-founded induction on lists via their length -/
protected def WellFounded.recAux {A : Type _} {B : List A -> Type _}
  (ih : ∀ l : List A, (∀ m : List A, List.length m < List.length l -> B m) -> B l) :
  ∀ l : List A, (∀ m : List A, List.length m < List.length l -> B m)
| []     => fun _ p => Empty.elim (Nat.notLtZero p)
| a :: l => fun m p => match Nat.Le_LtorEq p with
  | Sum.inl p => WellFounded.recAux ih l m (Nat.PredLtPred p)
  | Sum.inr p => by apply ih m
                    intros m' q
                    apply WellFounded.recAux ih l m'
                    exact (Ap Nat.pred p) ▸[fun n => List.length m' < n] q

protected def WellFounded.rec {A : Type _} {B : List A -> Type _} :
  (∀ l : List A, (∀ m : List A, List.length m < List.length l -> B m) -> B l) ->
  ∀ l : List A, B l :=
fun ih l => match l with
            | []     => ih [] (fun _ p => Empty.elim (Nat.notLtZero p))
            | a :: l => WellFounded.recAux ih (a :: a :: l) (a :: l) Nat.Le.refl

/- merge two lists such that two list ordered by a relation yield an ordered list
   containing the elements of both list. -/
@[match_pattern, reducible]
def merge {A : Type _} (R : A -> A -> Type _) [decR : DecidableRel R] :
  List A -> List A -> List A
| []    , m      => m
| a :: l, []     => a :: l
| a :: l, b :: m => match decR a b with
                    | Decidable.isTrue _  => a :: merge R l (b :: m)
                    | Decidable.isFalse _ => b :: merge R (a :: l) m

def merge_r {A : Type _} (R : A -> A -> Type _) [decR : DecidableRel R] (m : List A) :
  merge R [] m = m := sorry --rfl --Ap (List.cons b) (merge_r R m)

def add_eq : n + 0 = n := rfl

--def merge_nat : merge Nat.Le [] [1] = [1] := rfl

/- mergesort : well-founded inductive construction and actual sorting algorithm -/
def mergeSortWF {A : Type _} (R : A -> A -> Type _) [DecidableRel R] :
  ∀ l : List A, (∀ m : List A, List.length m < List.length l -> List A) -> List A
| []          => fun _ => []
| [a]         => fun _ => [a]
| a :: b :: l => let ls := split (a :: b :: l)
                 have h : split (a :: b :: l) = ⟨ls.1, ls.2⟩ := rfl
                 fun ih => merge R (ih ls.1 (length_split_lt h).1)
                                   (ih ls.2 (length_split_lt h).2)

def mergeSort {A : Type _} (R : A -> A -> Type _) [DecidableRel R] :
  List A -> List A :=
List.WellFounded.rec (mergeSortWF R)

end List

end hott
