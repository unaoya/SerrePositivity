module
public import Mathlib.CategoryTheory.Triangulated.Functor

/-! # shiftした三角形の同型を加法的関手で移す補助構成子 -/
@[expose] public section
noncomputable section
universe u₁ u₂ v₁ v₂
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable {C : Type u₁} {E : Type u₂} [Category.{v₁} C] [Category.{v₂} E]
  [Preadditive C] [Preadditive E] [HasShift C ℤ] [HasShift E ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [∀ (n : ℤ), (shiftFunctor E n).Additive]

/-- shiftとの比較を含めて、三角形の同型を関手で移す。 -/
def triangleShiftMapIso (F : C ⥤ E) [F.Additive] [F.CommShift ℤ]
    (s : ℤ) (T T' : Triangle C) (e : (Triangle.shiftFunctor C s).obj T ≅ T') :
    (Triangle.shiftFunctor E s).obj (F.mapTriangle.obj T) ≅ F.mapTriangle.obj T' :=
  (F.mapTriangleCommShiftIso s).symm.app T ≪≫ F.mapTriangle.mapIso e

/-- 始域の三角形同型をshiftしてから、指定された比較同型へ合成する。 -/
def triangleShiftIsoTrans (s : ℤ) (T T' T'' : Triangle C) (e : T ≅ T')
    (e' : (Triangle.shiftFunctor C s).obj T' ≅ T'') :
    (Triangle.shiftFunctor C s).obj T ≅ T'' :=
  (Triangle.shiftFunctor C s).mapIso e ≪≫ e'

end SerrePositivity.DifferentialGraded
