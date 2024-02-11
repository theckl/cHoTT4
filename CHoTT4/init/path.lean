/- Ported from HoTT3 -/
import CHoTT4.init.path0

universe u

namespace hott

def idp {A : Type u} {a : A} := @rfl _ a
def idpath {A : Type u} (a : A) := @rfl _ a

end hott
