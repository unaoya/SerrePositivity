module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.KProjectiveProduct
public import SerrePositivity.HomologicalAlgebra.Resolution

/-! # 離散加群の導来対象を表すK射影的な分解

既存の射影分解を整数添字の複体へ延長し、増大射の擬同型と導来像の同型を構成する。
局所化対象から直積への射の検出に使う。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 離散加群の射影分解を整数添字の複体へ延長したもの。 -/
abbrev moduleResolutionComplex (M : ModuleCat.{u} R) : CochainComplex (ModuleCat.{u} R) ℤ :=
  extRes (projectiveResolution M)

/-- 延長した射影分解はK射影的。 -/
instance moduleResolutionComplex_isKProjective (M : ModuleCat.{u} R) :
    (moduleResolutionComplex R M).IsKProjective := by
  have : (moduleResolutionComplex R M).IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact extRes_isZero_X (projectiveResolution M)
  have (i : ℤ) : Projective ((moduleResolutionComplex R M).X i) :=
    extRes_projective (projectiveResolution M) i
  exact CochainComplex.isKProjective_of_projective _ 0

/-- 整数添字へ延長した射影分解の増大射。 -/
def moduleResolutionAugmentation (M : ModuleCat.{u} R) :
    moduleResolutionComplex R M ⟶ (CochainComplex.singleFunctor (ModuleCat R) 0).obj M :=
  HomologicalComplex.extendMap (projectiveResolution M).π embUp ≫
    (HomologicalComplex.extendSingleIso embUp M 0 0 embUp_f_zero).hom

instance moduleResolutionAugmentation_quasiIso (M : ModuleCat.{u} R) :
    QuasiIso (moduleResolutionAugmentation R M) := by
  dsimp [moduleResolutionAugmentation]
  infer_instance

/-- K射影的な分解の導来像と、零次数加群の導来対象との同型。 -/
def moduleResolutionDerivedIso (M : ModuleCat.{u} R) :
    DerivedCategory.Q.obj (moduleResolutionComplex R M) ≅ (moduleObjectFunctor R).obj M :=
  asIso (DerivedCategory.Q.map (moduleResolutionAugmentation R M))

end SerrePositivity.DerivedCompletion
