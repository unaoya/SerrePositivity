module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeSourceFrame
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.RightFrameReplacement

/-!
概要：E2 の実 dg 代数モデルから、比較用の関手的 right resolution を選ぶ。
方針：実自由 I/J の第二分解を、E2 の既存の反対解像構成へ渡す。
規約：実 AW frame を Reedy 自明増大の解像と同一視せず、分解を仮定入力にしない。
使われ方：E2-S (6) の rightFrameHom と元の AW 写像模型との選択比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory _root_.HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.Reedy
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R]

attribute [local instance] EInfinity.DGAlgebra.modelCategory EInfinity.DGAlgebra.hasColimits
  EInfinity.DGAlgebra.hasFiniteLimits EInfinity.DGAlgebra.hasTerminal

def nativeModelFibrationFactorization :
    MorphismProperty.FunctorialFactorizationData (trivialCofibrations (Mon (Complex R)))
      (fibrations (Mon (Complex R))) := by
  have : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u}
      (EInfinity.DGAlgebra.generatingCofibrations (R := R))
      (EInfinity.DGAlgebra.generatingTrivialCofibrations (R := R)) :=
    EInfinity.DGAlgebra.modelCategory_cofibrantlyGenerated R
  have := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.hasFunctorialFactorization_trivialCofibration_fibration
    (EInfinity.DGAlgebra.generatingCofibrations (R := R))
    (EInfinity.DGAlgebra.generatingTrivialCofibrations (R := R))
  exact MorphismProperty.functorialFactorizationData _ _

def nativeModelRightResolutionFamily :
    CofibrantResolutionFamily (C := (Mon (Complex R))ᵒᵖ) simplex :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameFamilyOfFactorization (nativeModelFibrationFactorization R)

def nativeCellChosenRightMappingFunctor (A : Mon (Complex R)) : Mon (Complex R) ⥤ SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom (nativeModelRightResolutionFamily R) (cellResolution R A)

lemma nativeCellChosenRightMapping_kanComplex (A B : Mon (Complex R)) :
    SSet.KanComplex ((nativeCellChosenRightMappingFunctor R A).obj B) := by
  have := cellResolution_isCofibrant R A
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom_kanComplex (nativeModelRightResolutionFamily R)
    (cellResolution R A) B

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
