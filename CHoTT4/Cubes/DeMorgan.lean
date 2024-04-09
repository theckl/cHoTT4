import CHoTT4.Cubes.Direction

universe u

namespace hott

open Dir DirSet

namespace deMorgan

/- We introduce the free deMorgan algebra over a direction set by describing the elements
   and algebraic operations explicitly and then proving the axioms and (universal)
   properties of a (free) deMorgan algebra, instead of constructing it as an instance of
   a general structure and construction, with the axioms and properties implied.

   The reason is that we do not need other (free) de Morgan algebras, with the possible
   exception of subalgebras of the free DeMorgan algebras over direction sets. In that way,
   we also follow the model of introducing natural numbers: They form certainly a
   semiring, but the properties of their algebraic operations are proven from scratch. -/
@[reducible]
def head : List DirSetPair -> DirSetPair
| []        => ⟨noDirSet, noDirSet⟩
| (hd :: _) => hd

inductive is_ordered : List DirSetPair -> Type
| nil  : is_ordered []
| one  : is_ordered [⟨noDirSet, noDirSet⟩]
| cons : {T : List DirSetPair} -> {I : DirSetPair} -> (is_ordered T) -> (head T < I) ->
           is_ordered (I :: T)

inductive not_absorbing : List DirSetPair -> DirSetPair -> Type
| nil  : (I : DirSetPair) -> not_absorbing [] I
| tail : {T : List DirSetPair} -> {I J : DirSetPair} -> (not_absorbing T J) -> ¬(I ⊆ J) ->
           not_absorbing (I :: T) J

def absorbing_or_not : (T : List DirSetPair) -> (I : DirSetPair) ->
  not_absorbing T I ⊕ ¬(not_absorbing T I)
| []    , I => Sum.inl (not_absorbing.nil I)
| J :: T, I => match absorbing_or_not T I with
  | Sum.inl nabs => match isSubsetPair_or_not J I with
    | Sum.inl ss  => Sum.inr (fun nabs => match nabs with
                                         | not_absorbing.tail _ nss => nss ss)
    | Sum.inr nss => Sum.inl (not_absorbing.tail nabs nss)
  | Sum.inr abs  => Sum.inr (fun nabs => match nabs with
                                         | not_absorbing.tail nabs _ => abs nabs)

inductive is_normal : List DirSetPair -> Type
| nil  : is_normal []
| one  : is_normal [⟨noDirSet, noDirSet⟩]
| cons : {T : List DirSetPair} -> {I : DirSetPair} -> is_normal T -> head T < I ->
           not_absorbing T I -> is_normal (I :: T)

def normal_ord {T : List DirSetPair} : is_normal T -> is_ordered T
| is_normal.nil                => is_ordered.nil
| is_normal.one                => is_ordered.one
| is_normal.cons norm p _ => is_ordered.cons (normal_ord norm) p

inductive ofDirSet (I : DirSetPair) : (T : List DirSetPair) -> Type
| nil  : ofDirSet I []
| cons : {T : List DirSetPair} -> {J : DirSetPair} -> ofDirSet I T -> J ⊆ I ->
           ofDirSet I (J :: T)

/- The `nTerm`s are the normalized terms of the free deMorgan algebra over all
   directions. We define the join, meet and involution operations on these terms and
   prove their properties, but do not consider this algebra separately. Instead, we
   restrict the operations to the free deMorgan algberas over finite subsets of the
   directions, the only algebras needed.  -/
structure nTerm where
  L    : List DirSetPair
  norm : is_normal L

/- The 0-term of deMorgan algebras -/
@[match_pattern]
def dM0 := nTerm.mk [] is_normal.nil

/- The 1-term of deMorgan algebras -/
@[match_pattern]
def dM1 := nTerm.mk [⟨noDirSet, noDirSet⟩] is_normal.one

def joinMeet (I : DirSetPair) : nTerm -> List DirSetPair
| dM0                                            => [I]
| dM1                                            => dM1.L
| {L := J :: T, norm := is_normal.cons norm _ _} =>
  match DirSet.total_ltPair J I with
  | Sum.inr _ => match isSubsetPair_or_not I J with
    | Sum.inl _  => joinMeet I {L := T, norm := norm}
    | Sum.inr _  => J :: joinMeet I {L := T, norm := norm}
  | Sum.inl _ => match absorbing_or_not (J :: T) I with
    | Sum.inl _ => I :: J :: T
    | Sum.inr _ => J :: T

def joinMeet_is_normal : (I : DirSetPair) -> (T : nTerm) -> is_normal (joinMeet I T)
| ⟨noDirSet, noDirSet⟩                     , dM0 => is_normal.one
| ⟨DirSet.ext _ {list := _, ord := _} _, _⟩, dM0 =>
    is_normal.cons is_normal.nil (ltPair.first (lexLt.min _)) (not_absorbing.nil _)
| ⟨noDirSet, DirSet.ext _ {list := _, ord := _} _⟩, dM0 =>
    is_normal.cons is_normal.nil (ltPair.second rfl (lexLt.min _)) (not_absorbing.nil _)
| ⟨_, _⟩                                   , dM1 => dM1.norm
| ⟨I₁, I₂⟩, {L := J :: T, norm := is_normal.cons nT _ _} =>
  match DirSet.total_ltPair J ⟨I₁, I₂⟩ with
  | Sum.inr _ => match isSubsetPair_or_not ⟨I₁, I₂⟩ J with
    | Sum.inl _  => sorry --joinMeet_is_normal ⟨I₁, I₂⟩ {L := T, norm := nT}
    | Sum.inr _  => sorry
  | Sum.inl p => match absorbing_or_not (J :: T) ⟨I₁, I₂⟩ with
    | Sum.inl _ => sorry
    | Sum.inr _ => sorry

def join : nTerm -> nTerm -> nTerm
| dM0                                         , T => T
| dM1                                         , _ => dM1
| {L := I :: S, norm := is_normal.cons nS _ _}, T =>
     let T' := join {L := S, norm := nS} T
     {L := joinMeet I T', norm := joinMeet_is_normal I T'}

structure freeDeMorgan (I : DirSetPair) where
  T   : nTerm
  inI : ofDirSet I T.L

end deMorgan

end hott
