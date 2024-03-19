import CHoTT4.Init.Pathover
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

def lt_not_pt {i : Dir} : ¬(i < Dir.pt) := fun p => match i with
                                                    | Dir.pt => lt_irrefl _ p

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

def ge_Max {i j : Dir} (p : j ≤ i) : Max i j = i :=
  match le_lt_or_eq p with
  | Sum.inl q => gt_Max q
  | Sum.inr q => Eq.concat (Ap (Max i) q) (le_Max le.refl)

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

end Dir

open Dir
namespace DirSet

/- Direction sets: lists ordered by the order on `Dir`. -/
@[reducible]
def head : List Dir -> Dir
| []        => Dir.pt
| (hd :: _) => hd

def tail : List Dir -> List Dir
| []        => []
| (_ :: tl) => tl

inductive is_ordered : List Dir -> Type
| nil   : is_ordered []
| cons : (hd : Dir) -> (tl : List Dir) -> is_ordered tl -> head tl < hd ->
         is_ordered (hd::tl)

/- `is_ordered` is a proposition. -/
def is_ord_Eq : {I : List Dir} -> (ord₁ ord₂ : is_ordered I) -> ord₁ = ord₂
| [], is_ordered.nil, is_ordered.nil => rfl
| List.cons _ _, is_ordered.cons _ _ ord₁ _, is_ordered.cons _ _ ord₂ _ =>
    Ap011 (is_ordered.cons _ _) (is_ord_Eq ord₁ ord₂) (le_Eq _ _)

@[instance]
def is_ord_isProp {I : List Dir} : isProp (is_ordered I) := isProp.mk is_ord_Eq

structure DirSet where
  list : List Dir
  ord  : is_ordered list

@[reducible, match_pattern]
def noDirSet : DirSet := {list := [], ord := is_ordered.nil}

@[reducible, match_pattern]
def DirSet.ext (j : Dir) (tl : List Dir) (ord : is_ordered tl) (p : head tl < j) :
  DirSet :=
{list := j :: tl, ord := is_ordered.cons j tl ord p}

/- Equalities in `DirSet` are reducible to equalities of lists and therefore decidable. -/
def ListToDirSetEq : {I J : DirSet} -> I.list = J.list -> I = J
| {list := _, ord := _}, {list := _, ord := _} =>
    fun p => ApD011 _ p (PathoverOfTrEq p (isProp.elim _ _))

def List.Code : List Dir -> List Dir -> Type
| []    , []     => Unit
| []    , _ :: _ => Empty
| _ :: _, []     => Empty
| i :: I, j :: J => (i = j) × (List.Code I J)

def List.RCode : (I : List Dir) -> List.Code I I
| []     => Unit.unit
| _ :: I => ⟨rfl, List.RCode I⟩

def List.Encode {I J : List Dir} : (I = J) -> List.Code I J
| Eq.refl => List.RCode I

def List.nil_ne_cons {i : Dir} {I : List Dir} : ¬([] = i :: I) :=
  List.Encode

/- element relation of direction sets -/
inductive is_in : (j : Dir) -> (I : DirSet) -> Type
| noDir : is_in Dir.pt noDirSet
| prev  : (j i : Dir) -> (tl : List Dir) -> (ord : is_ordered tl) -> (p : head tl < i) ->
          is_in j {list := tl, ord := ord} -> is_in j (DirSet.ext i tl ord p)
| max   : (i : Dir) -> (tl : List Dir) -> (ord : is_ordered tl) -> (p : head tl < i) ->
          is_in i (DirSet.ext i tl ord p)

infix:55 " ∈ "  => is_in
notation:55 j:55 " ∉ " I:55 => ¬(j ∈ I)

def pt_is_in : (I : DirSet) -> Dir.pt ∈ I
| {list := []   , ord := is_ordered.nil}             => is_in.noDir
| {list := _::tl, ord := is_ordered.cons hd _ ord p} =>
    is_in.prev Dir.pt hd tl ord p (pt_is_in {list := tl, ord := ord})

def in_pt_pt : {j : Dir} -> j ∈ noDirSet -> j = Dir.pt
| Dir.pt, _ => rfl

def in_ext_eq_or_in {i j : Dir} {I : DirSet} {p : head I.list < i} :
  (in_ext : j ∈ DirSet.ext i I.list I.ord p) -> j = i ⊕ j ∈ I :=
fun in_ext => match in_ext with
| is_in.prev _ i _ _ _ el => Sum.inr el
| is_in.max i _ _ _       => Sum.inl rfl

def in_le_max {i : Dir} {I : DirSet} : i ∈ I -> i ≤ head I.list
| is_in.noDir => le.refl
| is_in.prev _ _ _ _ p el => le_trans (in_le_max el) (lt_le p)
| is_in.max i _ _ _ => @le.refl i

def in_prev_in {i j : Dir} {J : DirSet} {p : head J.list < j} :
  i ∈ DirSet.ext j J.list J.ord p -> i < j -> i ∈ J
| is_in.prev _ _ _ _ _ el => fun _ => el
| is_in.max _ _ _ _       => fun q => Empty.elim (lt_irrefl _ q)

def next_ni_noDir (i : Dir) : Dir.next i ∉ noDirSet :=
  fun el => next_ne_pt i (in_pt_pt el)

def ni_ne_pt {j : Dir} {I : DirSet} : j ∉ I -> j ≠ Dir.pt :=
  fun nel p => nel (p⁻¹ ▸[fun j => j ∈ I] pt_is_in I)

def ni_ext_ne {j j' : Dir} {I : DirSet} (p : head I.list < j) :
  j' ∉ DirSet.ext j I.list I.ord p -> j' ≠ j :=
fun nel q => nel (q⁻¹ ▸[fun (i : Dir) => i ∈ DirSet.ext j I.list I.ord p]
                                                         (@is_in.max j _ _ p))

def ni_ext_ni {j j' : Dir} {I : DirSet} {p : head I.list < j} :
  j' ∉ DirSet.ext j I.list I.ord p -> j' ∉ I :=
fun nel el => nel (is_in.prev j' j _ _ p el)

def ni_ne_ni_ext {i j : Dir} {I : DirSet} {p : head I.list < i } :
  j ≠ i -> j ∉ I -> j ∉ DirSet.ext i I.list I.ord p :=
fun np nel el_ext => match in_ext_eq_or_in el_ext with
                     | Sum.inl p  => np p
                     | Sum.inr el => nel el

/- element relation of directions in direction sets is decidable-/
def is_in_isDec : (j : Dir) -> (I : DirSet) -> Decidable (j ∈ I)
| Dir.pt    , _ => Decidable.isTrue (pt_is_in _)
| Dir.next _, {list := [], ord := is_ordered.nil} => Decidable.isFalse (next_ni_noDir _)
|          j, {list := i::tl, ord := is_ordered.cons _ _ ord p} =>
  match is_in_isDec j {list := tl, ord := ord} with
  | Decidable.isTrue el   => Decidable.isTrue (is_in.prev j i _ _ _ el)
  | Decidable.isFalse nel =>
    match Dir_has_DecidableEq j i with
    | Decidable.isTrue q   => Decidable.isTrue (q⁻¹ ▸[fun j => j ∈ _]
                                                 (is_in.max i tl ord p))
    | Decidable.isFalse nq => Decidable.isFalse (ni_ne_ni_ext nq nel)

/- size of direction sets -/
def Size (I : DirSet) : Nat := List.length I.list

/- the minimal element of a direction set -/
def SetMin : (I : DirSet) -> Dir
| {list := [], ord := is_ordered.nil} => Dir.pt
| {list := _::tl, ord := is_ordered.cons _ _ ord _} => SetMin {list := tl, ord := ord}

/- a new direction not in a given direction set -/
def Next : (I : DirSet) -> Dir
| {list := [], ord := is_ordered.nil} => Dir.next Dir.pt
| {list := hd::_, ord := is_ordered.cons _ _ _ _} => Dir.next hd

/- extending a direction set by a new direction -/
def extend : (j : Dir) -> (I : DirSet) -> DirSet :=
  fun j I => (extMax j I).1 where
extMax : (j : Dir) -> (I : DirSet) -> Σ (Ij : DirSet), Max j (head I.list) = head Ij.list
| Dir.pt    , I => ⟨I, Eq.concat (le_Max (pt_is_min _)) rfl⟩
| Dir.next j, {list := [], ord := is_ordered.nil} =>
    ⟨DirSet.ext (Dir.next j) [] is_ordered.nil (pt_lt_next _),
                                                   Eq.concat (ge_Max (pt_is_min _)) rfl⟩
| j         , {list := i :: I, ord := is_ordered.cons _ _ ord p} =>
  match le_total j i with
  | Sum.inl q =>
    match le_lt_or_eq q with
    | Sum.inl r => ⟨DirSet.ext i (extMax j {list := I, ord := ord}).1.list
                      (extMax j {list := I, ord := ord}).1.ord
                      ((extMax j {list := I, ord := ord}).2 ▸[fun k => k < i]
                                                           (lt_lt_Max_lt r p)), le_Max q⟩
    | Sum.inr _ => ⟨DirSet.ext i I ord p, le_Max q⟩
  | Sum.inr r => ⟨DirSet.ext j (DirSet.ext i I ord p).list (DirSet.ext i I ord p).ord r,
                  gt_Max r⟩

/- union of direction sets -/
def Union (I : DirSet ) : (J : DirSet) -> DirSet
| {list := [], ord := is_ordered.nil} => I
| {list := j::J, ord := is_ordered.cons _ _ ord _} =>
    Union (extend j I) {list := J, ord := ord}

/- intersection of direction sets -/
def Intersection : (I : DirSet) -> (J : DirSet) -> DirSet
| {list := [], ord := is_ordered.nil}, _ => noDirSet
| _, {list := [], ord := is_ordered.nil} => noDirSet
| {list := _::I, ord := is_ordered.cons _ _ ordI _},
       {list := j::J, ord := is_ordered.cons _ _ ordJ _} =>
  match is_in_isDec j {list := I, ord := ordI} with
  | Decidable.isTrue _   =>
             extend j (Intersection {list := I, ord := ordI} {list := J, ord := ordJ})
  | Decidable.isFalse _ => Intersection {list := I, ord := ordI} {list := J, ord := ordJ}

def subtract (j : Dir) : (I : DirSet) -> DirSet
| {list := [], ord := is_ordered.nil} => noDirSet
| {list := i::I, ord := is_ordered.cons _ _ ord _} =>
  match Dir_has_DecidableEq i j with
  | Decidable.isTrue _ => {list := I, ord := ord}
  | Decidable.isFalse _ => extend i (subtract j {list := I, ord := ord})

/- subset relation on direction sets -/
inductive isSubset : DirSet -> DirSet -> Type
| min : (J : DirSet) -> isSubset noDirSet J
| ext  : {I : DirSet} -> {i : Dir} -> {J : DirSet} -> (p : head I.list < i) ->
           (isSubset I J) -> (i ∈ J) -> isSubset (DirSet.ext i I.list I.ord p) J

infix:55 " ⊆ "  => isSubset
notation:55 I:55 " ⊈ " J:55 => ¬(I ⊆ J)

def isSubset_ElemImp {I J : DirSet} : I ⊆ J -> forall i : Dir, i ∈ I -> i ∈ J
| isSubset.min J => fun _ el => (in_pt_pt el)⁻¹ ▸[fun i => i ∈ J] pt_is_in J
| isSubset.ext p ss el => fun i ext_el =>
  match ext_el with
  | is_in.prev _ _ _ _ _ eli => isSubset_ElemImp ss i eli
  | is_in.max _ _ _ _ => el

def ElemImp_isSubset : {I J : DirSet} -> (forall i : Dir, i ∈ I -> i ∈ J) -> I ⊆ J
| noDirSet             , J => fun _ => isSubset.min J
| DirSet.ext i tl ord p, J => fun el_imp =>
    @isSubset.ext {list := tl, ord := ord} i J p
      (ElemImp_isSubset (fun j el => el_imp j (is_in.prev j i _ _ _ el))) (el_imp i (is_in.max i _ _ _))

def isSubset.refl (I : DirSet) : I ⊆ I :=
  ElemImp_isSubset (fun _ el => el)

def isSubset.trans {I J K : DirSet} : I ⊆ J -> J ⊆ K -> I ⊆ K
| isSubset.min _     => fun _  => isSubset.min K
| isSubset.ext p ss_IJ el => fun ss_JK => isSubset.ext p (isSubset.trans ss_IJ ss_JK)
                                                         (isSubset_ElemImp ss_JK _ el)

def minSubset {I : DirSet} : I ⊆ noDirSet -> I = noDirSet
| isSubset.min _      => rfl
| isSubset.ext p _ el => Empty.elim (lt_not_pt (in_pt_pt el ▸[fun i : Dir => _ < i] p))

def restrSubset {I J : DirSet} {j : Dir} {p : head J.list < j} :
  I ⊆ DirSet.ext j J.list J.ord p -> head I.list < j -> I ⊆ J
| isSubset.min _     => fun _ => isSubset.min _
| isSubset.ext q ss el => fun r => isSubset.ext q (restrSubset ss (lt_trans q r))
                                                  (in_prev_in el r)


/- disjoint direction sets -/
inductive disjointDirSets (I : DirSet) : (J : DirSet) -> Type
| disj : {j : Dir} -> {J : DirSet} -> (p : head J.list < j) -> (disjointDirSets I J) ->
         j ∉ I -> disjointDirSets I (DirSet.ext j J.list J.ord p)

open Algebra

/- lexicographic order on direction sets -/
inductive lexLt : DirSet -> DirSet -> Type
| min   : {I : DirSet} -> {i : Dir} -> (p : head I.list < i) ->
             lexLt noDirSet (DirSet.ext i I.list I.ord p)
| first : (I J : DirSet) -> {i j : Dir} -> (p : head I.list < i) -> (q : head J.list < j) ->
              (i < j) -> lexLt (DirSet.ext i I.list I.ord p) (DirSet.ext j J.list J.ord q)
| next  : {I J : DirSet} -> {i : Dir} -> (p : head I.list < i) -> (q : head J.list < i) ->
           (lexLt I J) -> lexLt (DirSet.ext i I.list I.ord p) (DirSet.ext i J.list J.ord q)

@[instance]
def DirSet_hasLt : hasLt DirSet := hasLt.mk lexLt

/- `lexLt` is a total order. -/
def total_lexLt : (I J : DirSet) -> (I < J ⊕ I = J) ⊕ J < I
| noDirSet, noDirSet => Sum.inl (Sum.inr rfl)
| noDirSet, DirSet.ext hd tl ord p =>
    Sum.inl (Sum.inl (@lexLt.min {list := tl, ord := ord} _ p))
| DirSet.ext hd tl ord p, noDirSet =>
    Sum.inr ((@lexLt.min {list := tl, ord := ord} _ p))
| DirSet.ext i I ordI pI, DirSet.ext j J ordJ pJ => match le_total i j with
  | Sum.inl q => match le_lt_or_eq q with
    | Sum.inl q => Sum.inl (Sum.inl (lexLt.first {list := I, ord := ordI}
                                                 {list := J, ord := ordJ} pI pJ q))
    | Sum.inr q =>
      match total_lexLt {list := I, ord := ordI} {list := J, ord := ordJ} with
      | Sum.inl r => match r with
        | Sum.inl r => by apply fun p => Sum.inl (Sum.inl p)
                          apply @Transport _ (fun K : DirSet => _ < K)
                                  (DirSet.ext i J ordJ (q⁻¹ ▸[fun j => head _ < j] pJ)) _
                          . apply ListToDirSetEq
                            exact (Ap (fun k => k :: J) q)
                          . exact @lexLt.next {list := I, ord := ordI} _ _ pI
                                                  (q⁻¹ ▸[fun j => head _ < j] pJ) r
        | Sum.inr r => Sum.inl (Sum.inr (ListToDirSetEq
                                               (Ap011 List.cons q (Ap DirSet.list r))))
      | Sum.inr r => by apply Sum.inr
                        apply @Transport _ (fun K : DirSet => _ < K)
                                    (DirSet.ext j I ordI (q ▸[fun j => head _ < j] pI)) _
                        . apply ListToDirSetEq
                          exact (Ap (fun k => k :: I) q⁻¹)
                        . exact @lexLt.next {list := J, ord := ordJ} _ _ pJ
                                                  (q ▸[fun j => head _ < j] pI) r
  | Sum.inr q => Sum.inr (lexLt.first {list := J, ord := ordJ} {list := I, ord := ordI}
                                      pJ pI q)

def lexLt_neq : {I J : DirSet} -> I < J -> I ≠ J
| noDirSet          , DirSet.ext _ _ _ _, _                          => fun p =>
    List.nil_ne_cons (Ap DirSet.list p)
| DirSet.ext _ _ _ _, DirSet.ext _ _ _ _, @lexLt.first _ _ _ _ _ _ q => fun p =>
    lt_ne q (Ap head (Ap DirSet.list p))
| DirSet.ext _ _ _ _, DirSet.ext _ _ _ _, lexLt.next q r s           => fun p =>
    lexLt_neq s (ListToDirSetEq (Ap tail (Ap DirSet.list p)))

def isSubset_lexLe : {I J : DirSet} -> I ⊆ J -> (I < J ⊕ I = J)
| _       , noDirSet             , ss                          => Sum.inr (minSubset ss)
| noDirSet, DirSet.ext j tl ord p, _                           =>
                                      Sum.inl (@lexLt.min {list := tl, ord := ord} j p)
| _       , DirSet.ext j tl ord p, @isSubset.ext I i _ q ss el =>
  match le_lt_or_eq (in_le_max el) with
  | Sum.inl r => Sum.inl (lexLt.first I {list := tl, ord := ord} _ _ r)
  | Sum.inr r =>
    match isSubset_lexLe (@restrSubset _ {list := tl, ord := ord} j _ ss (r ▸ q)) with
    | Sum.inl s => by apply Sum.inl
                      apply @Transport _ (fun K : DirSet => _ < K)
                                  (DirSet.ext i tl ord (r⁻¹ ▸[fun j => head _ < j] p)) _
                      . apply ListToDirSetEq
                        exact (Ap (fun k => k :: _) r)
                      . exact @lexLt.next I {list := tl, ord := ord} _ q
                                                        (r⁻¹ ▸[fun j => head _ < j] p) s
    | Sum.inr s => Sum.inr (ListToDirSetEq (Ap011 List.cons r (Ap DirSet.list s)))

/- When constructing the free deMorgan algebra over direction sets, we need pairs of
   direction sets, the first component associated to variables and the second to their
   involution. The subset relation and the lex order on direction sets induces a subset
   relation and an order on these pairs. -/
def DirSetPair := DirSet × DirSet

inductive isSubsetPair : DirSetPair -> DirSetPair -> Type
| comp_ss : {I J : DirSetPair} -> I.1 ⊆ J.1 -> I.2 ⊆ J.2 -> isSubsetPair I J

infix:55 " ⊆ "  => isSubsetPair
notation:55 I:55 " ⊈ " J:55 => ¬(I ⊆ J)

inductive ltPair : DirSetPair -> DirSetPair -> Type
| first  : {I J : DirSetPair} -> I.1 < J.1 -> ltPair I J
| second : {I J : DirSetPair} -> I.1 = J.1 -> I.2 < J.2 -> ltPair I J

@[instance]
def DirSetPair_hasLt : hasLt DirSetPair := hasLt.mk ltPair

def total_ltPair (I J : DirSetPair) : (I < J ⊕ I = J) ⊕ J < I :=
 match total_lexLt I.1 J.1 with
 | Sum.inl p => match p with
   | Sum.inl p => Sum.inl (Sum.inl (ltPair.first p))
   | Sum.inr p => match total_lexLt I.2 J.2 with
     | Sum.inl q => match q with
       | Sum.inl q => Sum.inl (Sum.inl (ltPair.second p q))
       | Sum.inr q => Sum.inl (Sum.inr (eqPair p q))
     | Sum.inr q => Sum.inr (ltPair.second p⁻¹ q)
 | Sum.inr p => Sum.inr (ltPair.first p)

def ltPair_neq {I J : DirSetPair} : I < J -> I ≠ J
| ltPair.first p    => fun q => lexLt_neq p (Ap Prod.fst q)
| ltPair.second _ q => fun r => lexLt_neq q (Ap Prod.snd r)

def isSubset_lePair {I J : DirSetPair} : I ⊆ J -> (I < J ⊕ I = J)
| isSubsetPair.comp_ss i₁ i₂ => match isSubset_lexLe i₁ with
  | Sum.inl p => Sum.inl (ltPair.first p)
  | Sum.inr p => match isSubset_lexLe i₂ with
    | Sum.inl q => Sum.inl (ltPair.second p q)
    | Sum.inr q => Sum.inr (eqPair p q)

end DirSet

end hott
