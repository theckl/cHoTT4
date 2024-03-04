import CHoTT4.Init.Logic
import CHoTT4.Algebra.Order
import CHoTT4.Init.Trunc

universe u

namespace hott

open isTrunc

namespace Dir

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
    | Decidable.isTrue p   => Decidable.isTrue (Ap Dir.next p)
    | Decidable.isFalse np => Decidable.isFalse (fun p => np (Ap Dir.prev p))

def next_ne_pt : ∀ (i : Dir), ¬(Dir.next i = Dir.pt) :=
  fun _ => encodeDir


open Algebra

/- order of directions -/
inductive le (i : Dir) : Dir → Type
| refl : le i i
| step : {j : Dir} -> le i j -> le i (Dir.next j)

@[instance]
def Dir_hasLe : hasLe Dir := hasLe.mk le

def lt (i j : Dir) := le (Dir.next i) j

@[instance]
def Dir_hasLt : hasLt Dir := hasLt.mk lt

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

/- `≤` and `<` -/
def lt_le : ∀ {i j : Dir}, i < j -> i ≤ j :=
  fun p => le_trans (le.step (refl _)) p

def next_le_next {i j : Dir} : (i ≤ j) -> Dir.next i ≤ Dir.next j
| le.refl => le.refl
| le.step p => le.step (next_le_next p)

/- transitivity of `<` -/
def lt_trans {i j k : Dir} (p : i < j) (q : j < k) : i < k :=
  le_trans p (le_trans (le_next _) q)

def pt_lt_next (i : Dir) : Dir.pt < Dir.next i := next_le_next (pt_is_min i)

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

/- Inequalities of directions are propositions. -/
def le_Eq : {i j : Dir} -> (p q : i ≤ j) ->  p = q
  | _, _, le.refl, le.refl  => rfl
  | _, _, le.refl, (@le.step _ _ q') => Empty.elim (not_next_le_self _ q')
  | _, _, (@le.step _ _ p'), le.refl => Empty.elim (not_next_le_self _ p')
  | _, _, (@le.step _ _ p'), (@le.step _ _ q') => Ap le.step (le_Eq p' q')

@[instance]
def le_isProp {i j : Dir} : isProp (i ≤ j) := isProp.mk le_Eq

/- anti-symmetry of `≤` -/
def le_antisymm {i j : Dir} : i ≤ j -> j ≤ i -> i = j
| le.refl  => fun _ => IdP
| @le.step i j p => fun q => Empty.elim (lt_irrefl j (le_trans q p))

/- total order -/
def le_total : ∀ (i j : Dir), i ≤ j ⊕ j < i
| Dir.pt,     Dir.pt     => Sum.inl le.refl
| Dir.pt,     Dir.next _ => Sum.inl (pt_is_min _)
| Dir.next _, Dir.pt     => Sum.inr (pt_lt_next _)
| Dir.next i, Dir.next j => match le_total i j with
                            | Sum.inl p => Sum.inl (next_le_next p)
                            | Sum.inr p => Sum.inr (next_le_next p)

def le_total_l {i j : Dir} (p : i ≤ j) : le_total i j = Sum.inl p :=
  match le_total i j with
  | Sum.inl _ => Ap Sum.inl (le_Eq _ _)
  | Sum.inr q => Empty.elim (not_next_le_self j (le_trans q p))

def le_total_r {i j : Dir} (p : j < i) : le_total i j = Sum.inr p :=
  match le_total i j with
  | Sum.inl q => Empty.elim (not_next_le_self j (le_trans p q))
  | Sum.inr _ => Ap Sum.inr (le_Eq _ _)

def lt_ne : ∀ {i j : Dir}, i < j -> i ≠ j :=
  fun p q => match q with | Eq.refl => lt_irrefl _ p

def le_ne_lt {i j : Dir} : i ≤ j -> i ≠ j -> i < j
| le.refl => fun q => Empty.elim (q IdP)
| le.step p => fun _ => next_le_next p

def le_lt_or_eq {i j : Dir} : i ≤ j -> i < j ⊕ i = j
| le.refl => Sum.inr IdP
| le.step p => Sum.inl (next_le_next p)

def ne_lt_or_gt {i j : Dir} : i ≠ j -> (i < j ⊕ j < i) :=
  fun np => match le_total i j with
            | Sum.inl q => Sum.inl (le_ne_lt q np)
            | Sum.inr q => Sum.inr q

/- maximum of two directions -/
@[reducible]
def Max (i j : Dir) : Dir :=
  leMax i j (le_total i j)
where
  leMax (i j : Dir) : (i ≤ j ⊕ j < i) -> Dir
  | Sum.inl _ => j
  | Sum.inr _ => i

def le_Max {i j : Dir} : i ≤ j -> Max i j = j :=
  fun p => @Eq.concat _ (Max.leMax i j (le_total i j)) (Max.leMax i j (Sum.inl p)) _
                      (Ap (Max.leMax i j) (le_total_l p)) rfl

def gt_Max {i j : Dir} : j < i -> Max i j = i :=
  fun p => @Eq.concat _ (Max.leMax i j (le_total i j)) (Max.leMax i j (Sum.inr p)) _
                      (Ap (Max.leMax i j) (le_total_r p)) rfl

def Max_l (i j : Dir) : i ≤ Max i j :=
  leMax_l i j
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
      | Sum.inr q => lt_le q

def lt_lt_Max_lt {i j k : Dir} : i < k -> j < k -> Max i j < k :=
  match (le_total i j) with
  | Sum.inl r => fun _ q => (le_Max r)⁻¹ ▸[fun i => i < k] q
  | Sum.inr r => fun p _ => (gt_Max r)⁻¹ ▸[fun i => i < k] p


/- Direction sets: an inductive family, to record the maximal element. -/
inductive DirSet : Dir -> Type
| noDir : DirSet Dir.pt
| ext : {i : Dir} -> DirSet i -> (j : Dir) -> {_ : i < j} -> DirSet j

/- elements of direction sets -/
inductive is_in : (j : Dir) -> {i : Dir} -> (I : DirSet i) -> Type
| prev : (j : Dir) -> {i i': Dir} -> (I : DirSet i) -> (p : i < i') -> is_in j I ->
         is_in j (@DirSet.ext i I i' p)
| max : @is_in i i I

infix:55 " ∈ "  => is_in
notation:55 j:55 " ∉ " I:55 => ¬(j ∈ I)

def pt_is_in {i : Dir} : (I : DirSet i) -> Dir.pt ∈ I
| DirSet.noDir => is_in.max
| @DirSet.ext _ I j p => is_in.prev Dir.pt I p (pt_is_in I)

def ni_ne_pt {i j : Dir} {I : DirSet i} : j ∉ I -> j ≠ Dir.pt :=
  fun np q => Empty.elim ((q ▸[fun (i : Dir) => (i ∉ I)] np) (pt_is_in I))

def ni_ext_ne {i j j' : Dir} {I : DirSet i} {p : i < j} :
  j' ∉ @DirSet.ext _ I j p -> j ≠ j' :=
fun nel el => nel (el ▸[fun (i' : Dir) => i' ∈ DirSet.ext I j]
                                                    (@is_in.max j (DirSet.ext I j)))

def ni_ext_ni {i j j' : Dir} {I : DirSet i} {p : i < j } :
  j' ∉ @DirSet.ext _ I j p -> j' ∉ I :=
fun nel el => nel (is_in.prev j' I p el)

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

/- Extending a direction set by one new direction -/
def extend {i : Dir} :
  (I : DirSet i) -> (j : Dir) -> {_ : j ∉ I} -> DirSet (Max i j)
| DirSet.noDir => fun j nel => by
    apply @DirSet.ext _ DirSet.noDir (Max Dir.pt j)
    exact le_trans (le_ne_lt (pt_is_min j) (ni_ne_pt nel)⁻¹) (Max_r _ j)
| @DirSet.ext _ I j' q =>
    fun j nel => match ne_lt_or_gt (ni_ext_ne nel) with
                 | Sum.inl p => (le_Max (lt_le p))⁻¹ ▸[fun i => DirSet i]
                                @DirSet.ext _ (@DirSet.ext _ I j' q) j p
                 | Sum.inr p => (gt_Max p)⁻¹ ▸[fun i => DirSet i]
                                @DirSet.ext _ (@extend _ I j (ni_ext_ni nel)) j'
                                            (lt_lt_Max_lt q p)

/- union of direction sets -/
def Union {i j : Dir} : DirSet i -> DirSet j -> DirSet (Max i j)
| DirSet.noDir        , DirSet.noDir         => DirSet.noDir
| DirSet.noDir        , @DirSet.ext _ J j' q =>
    @DirSet.ext _ J (Max Dir.pt j') (le_trans q (Max_r _ _))
| @DirSet.ext _ I i' p, DirSet.noDir         =>
    @DirSet.ext _ I  (Max i' Dir.pt) (le_trans p (Max_l _ _))
| @DirSet.ext i I i' p, @DirSet.ext j J j' q =>
  match le_total i' j' with
  | Sum.inl r =>
    match le_lt_or_eq r with
    | Sum.inl r => (le_Max (lt_le r))⁻¹ ▸[fun i => DirSet i]
                   DirSet.ext (DirSet.ext (Union I J) i') j'
    | Sum.inr r => sorry
  | Sum.inr r => sorry

end Dir

end hott
