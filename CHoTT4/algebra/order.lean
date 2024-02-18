/- Ported from HoTT3 -/
universe u

namespace hott

namespace algebra

/- orders -/

class has_le (α : Type u) := (le : α → α → Type u)
class has_lt (α : Type u) := (lt : α → α → Type u)

infix:55 " ≤ "  => has_le.le
infix:55 " < "  => has_lt.lt

end algebra

end hott
