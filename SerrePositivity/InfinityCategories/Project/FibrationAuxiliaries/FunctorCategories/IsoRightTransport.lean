module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.IsoTriangleIdentity

/-!
概要：対象の等式による右端の表示変更は、元の指定同型の値を保持する。
方針：対象の等式を消去し、恒等同型との合成を簡約する。
規約：指定同型を選び直さない。
使われ方：大域制限の厳密な可換式から来る終点補正を外す。
-/

@[expose] public section
universe u v
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 対象の等式による右端の表示変更は、元の同型と同じ値。 -/
lemma iso_trans_eqToIso_heq {C : Type u} [Category.{v} C] {a b c : C}
    (e : a ≅ b) (h : b = c) : HEq (e ≪≫ eqToIso h) e := by
  subst c
  simp only [eqToIso_refl, Iso.trans_refl]
  rfl

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
