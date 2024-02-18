import CHoTT4.init.logic
import CHoTT4.algebra.order

universe u

namespace hott

namespace dir

/- Directions -/
inductive Dir : Type
| pt : Dir
| next : Dir -> Dir
deriving Repr

def Dir.prev : Dir -> Dir
| Dir.pt => Dir.pt
| Dir.next i => i

/- Equality between directions is decidable. -/
def Code : Dir -> Dir -> Type
| Dir.pt,     Dir.pt     => Unit
| Dir.pt,     Dir.next _ => Empty
| Dir.next _, Dir.pt     => Empty
| Dir.next i, Dir.next j => Code i j

def RCode : (i : Dir) -> Code i i
| Dir.pt => Unit.unit
| Dir.next i => RCode i

def encodeDir {i j : Dir} : i = j -> Code i j
| Eq.refl => RCode i

@[instance]
def Dir_has_DecidableEq : DecidableEq Dir
| Dir.pt,     Dir.pt     => Decidable.isTrue rfl
| Dir.pt,     Dir.next _ => Decidable.isFalse (fun p => encodeDir p)
| Dir.next _, Dir.pt     => Decidable.isFalse (fun p => encodeDir p)
| Dir.next i, Dir.next j =>
    match Dir_has_DecidableEq i j with
    | Decidable.isTrue p   => Decidable.isTrue (ap Dir.next p)
    | Decidable.isFalse np => Decidable.isFalse (fun p => np (ap Dir.prev p))

def next_ne_pt : ∀ (i : Dir), ¬(Dir.next i = Dir.pt) :=
  fun _ => encodeDir

open algebra


/- order of directions -/
inductive le (i : Dir) : Dir → Type
| refl : le i i
| step : {j : Dir} -> le i j -> le i (Dir.next j)

@[instance]
def Dir_has_le : has_le Dir := has_le.mk le

def lt (i j : Dir) := le (Dir.next i) j

@[instance]
def Dir_has_lt : has_lt Dir := has_lt.mk lt

/- minimality of `pt` -/
def pt_is_min : ∀ i : Dir, Dir.pt ≤ i
| Dir.pt     => le.refl
| Dir.next i => le.step (pt_is_min i)

def pt_is_min' : ∀ i : Dir, Dir.pt < Dir.next i
| Dir.pt     => le.refl
| Dir.next i => le.step (pt_is_min' i)

/- minimality of `next i` among all directions stricly larger than `i` -/
def next_is_min {i j : Dir} : i < j -> Dir.next i ≤ j :=
  fun lt_ij => lt_ij

def le_next (i : Dir) : i ≤ Dir.next i := le.step (le.refl)

/- reflexivity -/
def refl (i : Dir) : i ≤ i := le.refl

/- transitivity of `≤` -/
def le_trans {i j k : Dir} (p : i ≤ j) : (j ≤ k) -> i ≤ k
| le.refl => p
| @le.step j _ q => le.step (le_trans p q)

def next_le_next {i j : Dir} : (i ≤ j) -> Dir.next i ≤ Dir.next j
| le.refl => le.refl
| le.step p => le.step (next_le_next p)

def pred_le_pred {i j : Dir} : Dir.next i ≤ Dir.next j -> (i ≤ j)
| le.refl => le.refl
| le.step p => le_trans (le_next i) p

def next_le_not_pt {i j : Dir} : (p : Dir.next i ≤ j) -> ¬(j = Dir.pt)
| le.refl => next_ne_pt i
| le.step p => next_ne_pt _

def not_next_le_self : (i : Dir) -> ¬(Dir.next i ≤ i)
| Dir.pt => fun p => Empty.elim (next_le_not_pt p IdP)
| Dir.next i => fun p => not_next_le_self i (pred_le_pred p)

def lt_irrefl (i : Dir) : ¬(i < i) := not_next_le_self i

/- anti-symmetry of `≤` -/
def le_antisymm {i j : Dir} : i ≤ j -> j ≤ i -> i = j
| le.refl  => fun _ => IdP
| @le.step i j p => fun q => Empty.elim (lt_irrefl j (le_trans q p))

/- total order -/
def le_total : ∀ (i j : Dir), i ≤ j ⊕ j ≤ i
| Dir.pt,     Dir.pt     => Sum.inl le.refl
| Dir.pt,     Dir.next _ => Sum.inl (pt_is_min _)
| Dir.next _, Dir.pt     => Sum.inr (pt_is_min _)
| Dir.next i, Dir.next j => match le_total i j with
                            | Sum.inl p => Sum.inl (next_le_next p)
                            | Sum.inr p => Sum.inr (next_le_next p)

/- `≤` and `<` -/
def lt_le : ∀ {i j : Dir}, i < j -> i ≤ j :=
  fun p => le_trans (le.step (refl _)) p

def lt_ne : ∀ {i j : Dir}, i < j -> i ≠ j :=
  fun p q => match q with | Eq.refl => lt_irrefl _ p

def le_ne_lt {i j : Dir} : i ≤ j -> i ≠ j -> i < j
| le.refl => fun q => Empty.elim (q IdP)
| le.step p => fun _ => next_le_next p

def le_lt_or_eq {i j : Dir} : i ≤ j -> i < j ⊕ i = j
| le.refl => Sum.inr IdP
| le.step p => Sum.inl (next_le_next p)

/- maximum of two directions -/
@[reducible]
def Max (i j : Dir) : Dir :=
  leMax i j (le_total i j)
where
  leMax (i j : Dir) : (i ≤ j ⊕ j ≤ i) -> Dir
  | Sum.inl _ => j
  | Sum.inr _ => i

def Max_l (i j : Dir) : i ≤ Max i j := by
  exact leMax_l i j
where
  leMax_l (i j : Dir) : i ≤ Max.leMax i j (le_total i j) :=
    match (le_total i j) with
      | Sum.inl p => p
      | Sum.inr _ => le.refl

def Max_r (i j : Dir) : j ≤ Max i j := by
  exact leMax_r i j
where
  leMax_r (i j : Dir) : j ≤ Max.leMax i j (le_total i j) :=
    match (le_total i j) with
      | Sum.inl _ => le.refl
      | Sum.inr q => q

/- Direction sets: an inductive family, to record the maximal element. -/
inductive DirSet : Dir -> Type
| noDir : DirSet Dir.pt
| ext : {i : Dir} -> DirSet i -> (j : Dir) -> {_ : i < j} -> DirSet j

/- elements of direction sets -/
inductive is_in : (j : Dir) -> {i : Dir} -> (I : DirSet i) -> Type
| prev : {i' : Dir} -> (I' : DirSet i') -> (p : i' < i) -> is_in j I' -> is_in j I
| max : is_in i I

infix:55 " ∈ "  => is_in
notation:55 j:55 " ∉ " I:55 => ¬(j ∈ I)

def pt_is_in {i : Dir} : (I : DirSet i) -> Dir.pt ∈ I
| DirSet.noDir => is_in.max
| @DirSet.ext _ I j p => is_in.prev I p (pt_is_in I)

def nin_ne_pt {i j : Dir} {I : DirSet i} : j ∉ I -> j ≠ Dir.pt :=
  fun np q => Empty.elim ((q ▸[fun (i : Dir) => ¬(i ∈ I)] np) (pt_is_in I))

/- size -/
def Size {i : Dir} : (I : DirSet i) -> Nat
| DirSet.noDir => 0
| DirSet.ext I j => (Size I) + 1

/- minimal direction -/
def SetMin {i : Dir} : (I : DirSet i) -> Dir
| DirSet.noDir => Dir.pt
| DirSet.ext I j => SetMin I

/- next largest direction -/
def Next {i : Dir} : (I : DirSet i) -> Dir :=
  fun _ => Dir.next i

/- Extending a direction set by one direction -/
def extend {i : Dir} :
  (I : DirSet i) -> (j : Dir) -> {nel : ¬(j ∈ I)} -> DirSet (Max i j)
| DirSet.noDir => fun j nel => by
    apply @DirSet.ext _ DirSet.noDir (Max Dir.pt j)
    exact le_trans (le_ne_lt (pt_is_min j) (nin_ne_pt nel)⁻¹) (Max_r _ j)
| DirSet.ext I j' => sorry

/- union of direction sets -/
def Union {i j : Dir} : DirSet i -> DirSet j -> DirSet (Max i j)
| DirSet.noDir        , DirSet.noDir         => DirSet.noDir
| DirSet.noDir        , @DirSet.ext _ J j' q =>
    @DirSet.ext _ J (Max Dir.pt j') (le_trans q (Max_r _ _))
| @DirSet.ext _ I i' p, DirSet.noDir         =>
    @DirSet.ext _ I  (Max i' Dir.pt) (le_trans p (Max_l _ _))
| @DirSet.ext _ I i' p, @DirSet.ext _ J j' q => sorry

end dir

end hott
