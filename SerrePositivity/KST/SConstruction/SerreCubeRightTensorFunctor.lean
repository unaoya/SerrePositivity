module
public import SerrePositivity.KST.SConstruction.CubeLeftKeep

/-! # 元の Serre 射の右 tensor 関手
概要：元の Serre 射の右 tensor を、具体的立方体圏上の関手へ束ねる。
方針：元の Serre 関手と右 tensor 関手を合成する。
規約：射は元の tensor そのもの。使われ方：全生成語の右 tensor 比較の検証。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の Serre 関手の右 tensor。 -/
def serreCubeRightTensorFunctor : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube ⥤ Comon (Complex A) :=
  serreConcreteCubeFunctor A ⋙ tensorRight (serreIntervalComonoid A)

end SerrePositivity.KST.SConstruction
