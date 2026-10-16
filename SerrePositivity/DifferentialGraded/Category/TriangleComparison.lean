module
public import Mathlib.CategoryTheory.Triangulated.Functor

/-! # dg標準三角形の比較に使う第三射の評価 -/
@[expose] public section
noncomputable section
universe u v u' v'
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  [HasShift C ℤ] [HasShift D ℤ]

/-- 第三射の計算式を、shift整合関手が誘導する三角形の第三射の計算式へ運ぶ。 -/
lemma triangleComparison_mor₃ (F : C ⥤ D) [F.CommShift ℤ] (T : Triangle C)
    (f : T.obj₃ ⟶ T.obj₁⟦(1 : ℤ)⟧) (h : T.mor₃ = f) :
    (F.mapTriangle.obj T).mor₃ = F.map f ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁ :=
  congrArg (fun a => F.map a ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁) h

end SerrePositivity.DifferentialGraded
