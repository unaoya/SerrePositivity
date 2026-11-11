module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeCellModel
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexResolution

/-!
概要：E2 の実余生成モデルから、dg 代数の関手的な始域 frame を選ぶ。
方針：実自由 I/J の余生成から関手的分解を得て、既存の Reedy 分解へ代入する。
規約：分解データやモデル構造を入力せず、元の native cell 源への増大を保持する。
使われ方：実 cell 源と AW right frame の混合 Hom 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.Reedy
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R]

attribute [local instance] EInfinity.DGAlgebra.modelCategory EInfinity.DGAlgebra.hasColimits
  EInfinity.DGAlgebra.hasFiniteLimits

def nativeModelCofibrationFactorization :
    MorphismProperty.FunctorialFactorizationData (cofibrations (Mon (Complex R)))
      (trivialFibrations (Mon (Complex R))) := by
  have : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u}
      (EInfinity.DGAlgebra.generatingCofibrations (R := R))
      (EInfinity.DGAlgebra.generatingTrivialCofibrations (R := R)) :=
    EInfinity.DGAlgebra.modelCategory_cofibrantlyGenerated R
  have := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.hasFunctorialFactorization_cofibration_trivialFibration
    (EInfinity.DGAlgebra.generatingCofibrations (R := R))
    (EInfinity.DGAlgebra.generatingTrivialCofibrations (R := R))
  exact MorphismProperty.functorialFactorizationData _ _

def nativeModelSourceResolutionFamily : CofibrantResolutionFamily (C := Mon (Complex R)) simplex :=
  cosimplicialResolutionFamily (nativeModelCofibrationFactorization R)

def nativeCellSourceFrame (A : Mon (Complex R)) : SimplexCategory ⥤ Mon (Complex R) :=
  (nativeModelSourceResolutionFamily R).obj.obj (cellResolution R A)

def nativeCellSourceFrameAugmentation (A : Mon (Complex R)) :
    nativeCellSourceFrame R A ⟶ (Functor.const SimplexCategory).obj (cellResolution R A) :=
  (nativeModelSourceResolutionFamily R).augmentation.app (cellResolution R A)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
