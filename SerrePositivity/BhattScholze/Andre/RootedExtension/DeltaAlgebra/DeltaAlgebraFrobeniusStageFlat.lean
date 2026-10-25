module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.DeltaAlgebra.DeltaAlgebraFrobeniusStages
public import SerrePositivity.BhattScholze.Andre.RootedExtension.PerfectDeltaFrobeniusStageFlat

/-! # 正確な係数作用を持つ実δ環段の標準還元判定 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (D : DeltaStructure p A) (E : DeltaStructure p B) (j : A →+* B) (d : A) (n : ℕ)
local notation "Q₀" => A ⧸ Ideal.span {(p : A), d}
local notation "q₀" => Ideal.Quotient.mk (Ideal.span {(p : A), d})
local notation "X₀" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor
  (baseChangeScalarModule j)
local notation "Xₙ" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor
  (baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j n))
local notation "Y₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q₀) X₀
local notation "Yₙ" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q₀) Xₙ
local notation "Wₙ" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q₀)
  (CategoryTheory.Functor.obj (boundedAboveDerivedRestrictScalars (D.frobeniusLift ^ n)) X₀)

/-- 元の実δ環の還元入力から、全実環段（j_n作用）の標準還元の次数消滅を得る。 -/
theorem deltaAlgebraFrobeniusStageResidue_homology_isZero
    (hD : D.IsPerfect) (hj : D.IsDeltaHom E j)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj))
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Yₙ).obj) := by
  let e := (boundedAboveDerivedBaseChange q₀).mapIso
    (deltaAlgebraFrobeniusStageSingleIso D E j hj n).symm
  have hz := perfectDeltaFrobeniusTwistResidue_homology_isZero D hD d n X₀ hzero hFF i hi
  exact hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).mapIso
    (DerivedCategory.Minus.ι.mapIso e))

/-- 正確なj_n係数作用を持つ全実環段の、標準還元H0忠実平坦性。 -/
theorem deltaAlgebraFrobeniusStageResidueH0_faithfullyFlat
    (hD : D.IsPerfect) (hj : D.IsDeltaHom E j)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj)) :
    Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Yₙ).obj) := by
  let M := (DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Wₙ).obj
  let e := (boundedAboveDerivedBaseChange q₀).mapIso
    (deltaAlgebraFrobeniusStageSingleIso D E j hj n).symm
  let eH := (DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).mapIso
    (DerivedCategory.Minus.ι.mapIso e)
  have : Module.FaithfullyFlat Q₀ M :=
    perfectDeltaFrobeniusTwistResidueH0_faithfullyFlat D hD d n X₀ hzero hFF
  exact Module.FaithfullyFlat.of_linearEquiv Q₀ M eH.toLinearEquiv

/-- 同じ実環段の通常の標準剰余テンソルも、元のA/(p,d)上で忠実平坦。 -/
theorem deltaAlgebraFrobeniusStageResidueTensor_faithfullyFlat
    (hD : D.IsPerfect) (hj : D.IsDeltaHom E j)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj)) :
    Module.FaithfullyFlat Q₀ ((ModuleCat.extendScalars q₀).obj
      (baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j n))) := by
  let M := (DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Yₙ).obj
  have : Module.FaithfullyFlat Q₀ M :=
    deltaAlgebraFrobeniusStageResidueH0_faithfullyFlat D E j d n hD hj hzero hFF
  let e := (boundedAboveDerivedBaseChangeModuleH0Iso q₀).app
    (baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j n))
  exact Module.FaithfullyFlat.of_linearEquiv Q₀ M e.toLinearEquiv.symm

end SerrePositivity.BhattScholze
