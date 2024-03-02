/- Ported from HoTT3 -/
universe u

namespace hott

namespace Algebra

/- orders -/

class hasLe (α : Type u) := (le : α → α → Type u)
class hasLt (α : Type u) := (lt : α → α → Type u)

infix:55 " ≤ "  => hasLe.le
infix:55 " < "  => hasLt.lt

end Algebra

end hott
