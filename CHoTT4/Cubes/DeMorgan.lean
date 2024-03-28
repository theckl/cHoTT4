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
| cons : {T : List DirSetPair} -> {I : DirSetPair} -> (is_ordered T) -> (head T < I) ->
           is_ordered (I :: T)

inductive not_absorbing : List DirSetPair -> DirSetPair -> Type
| nil  : (I : DirSetPair) -> not_absorbing [] I
| tail : {T : List DirSetPair} -> {I J : DirSetPair} -> (not_absorbing T J) -> ¬(I ⊆ J) ->
           not_absorbing (I :: T) J

inductive is_normal : List DirSetPair -> Type
| nil  : is_normal []
| cons : {T : List DirSetPair} -> {I : DirSetPair} -> is_normal T -> head T < I ->
           not_absorbing T I -> is_normal (I :: T)

def normal_ord {T : List DirSetPair} : is_normal T -> is_ordered T
| is_normal.nil                => is_ordered.nil
| @is_normal.cons _ _ norm p _ => is_ordered.cons (normal_ord norm) p

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

def joinMeet : DirSetPair -> nTerm -> nTerm
| ⟨noDirSet, noDirSet⟩                        , {L := [], norm := _}    =>
    {L := [], norm := is_normal.nil}
| ⟨DirSet.ext i {list := I, ord := ordI} p, J⟩, {L := [], norm := nnil} =>
    {L := [⟨DirSet.ext i {list := I, ord := ordI} p, J⟩],
     norm := is_normal.cons nnil (ltPair.first (lexLt.min p)) (not_absorbing.nil _)}
| ⟨I, DirSet.ext j {list := J, ord := ordJ} q⟩, {L := [], norm := nnil} =>
    {L := [⟨I, DirSet.ext j {list := J, ord := ordJ} q⟩],
     norm := is_normal.cons nnil (match I with
                                  | noDirSet                                =>
                                      ltPair.second rfl (lexLt.min q)
                                  | DirSet.ext i {list := I, ord := ordI} p =>
                                      ltPair.first (lexLt.min p))
                                 (not_absorbing.nil _)}
| I                                          ,
                  {L := J :: T, norm := is_normal.cons norm p nabs}    => sorry

structure freeDeMorgan (I : DirSetPair) where
  T   : nTerm
  inI : ofDirSet I T.L

end deMorgan

end hott
