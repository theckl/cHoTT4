universe u

namespace hott

class Zero (α : Type u) where
  zero : α

instance (priority := 300) Zero.toOfNat0 {α} [Zero α] : OfNat α (nat_lit 0) where
  ofNat := ‹Zero α›.1

instance (priority := 200) Zero.ofOfNat0 {α} [OfNat α (nat_lit 0)] : Zero α where
  zero := 0

class One (α : Type u) where
  one : α

instance (priority := 300) One.toOfNat1 {α} [One α] : OfNat α (nat_lit 1) where
  ofNat := ‹One α›.1

instance (priority := 200) One.ofOfNat1 {α} [OfNat α (nat_lit 1)] : One α where
  one := 1

end hott
