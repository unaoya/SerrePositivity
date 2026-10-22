module

public import Mathlib.CategoryTheory.Iso

/-!
概要：固定した二つの指定同型の間での合成は、中央の指定同型の値を反映する。
方針：同じ二つの逆を合成して両外側因子を相殺する。
規約：指定値を選び直さない。使われ方：模型単位比較から元の raw fiber 比較を反映する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
namespace SerrePositivity.InfinityCategories.F2

/-- 固定した元の両外側同型による合成は、中央の指定同型の等式を反映する。 -/
lemma iso_sandwich_injective {C : Type u} [Category.{v} C] {a b c d : C}
    (l : a ≅ b) (r : c ≅ d) : Function.Injective (fun e : b ≅ c => l ≪≫ e ≪≫ r) := by
  intro e f h
  have h' := congrArg (fun t => (l.symm ≪≫ t) ≪≫ r.symm) h
  simp only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans] at h'
  simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using h'

end SerrePositivity.InfinityCategories.F2
