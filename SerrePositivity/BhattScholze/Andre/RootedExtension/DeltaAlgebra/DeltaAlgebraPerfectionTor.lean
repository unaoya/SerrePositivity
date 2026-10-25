module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.DeltaAlgebra.DeltaAlgebraFrobeniusStageFlat
public import SerrePositivity.BhattScholze.Andre.RootedExtension.DeltaAlgebra.DeltaAlgebraPerfectionCocone
public import SerrePositivity.HomologicalAlgebra.TorSequentialColimits

/-! # 実δ完全化へのG7の適用 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (D : DeltaStructure p A) (E : DeltaStructure p B) (j : A →+* B) (d : A)
local notation "Q₀" => A ⧸ Ideal.span {(p : A), d}
local notation "q₀" => Ideal.Quotient.mk (Ideal.span {(p : A), d})
local notation "X₀" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor
  (baseChangeScalarModule j)
local notation "Y₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q₀) X₀
local notation "M∞" => baseChangeScalarModule (deltaAlgebraPerfectionCoefficient E j)
local notation "X∞" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor M∞
local notation "Y∞" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q₀) X∞

/-- 各実δ環段の標準還元入力を、G7により実δ完全化の正のTorへ渡す。 -/
theorem deltaAlgebraPerfectionResidueTor_isZero
    (hD : D.IsPerfect) (hj : D.IsDeltaHom E j)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj))
    (n : ℕ) (hn : 0 < n) :
    IsZero (((ModuleCat.extendScalars q₀).leftDerived n).obj M∞) := by
  let H := (ModuleCat.extendScalars q₀).leftDerived n
  have hz : IsZero (H.obj (colimit (deltaAlgebraFrobeniusStageModuleDiagram E j))) := by
    apply torAlg_colimit_isZero_of_stages
    intro k
    let M := baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j k)
    let e := (DerivedCategory.homologyFunctor (ModuleCat Q₀) (-(n : ℤ))).mapIso
        (boundedAboveDerivedBaseChangeModuleIso q₀ M) ≪≫
      (derivedModuleBaseChangeHomologyIso q₀ n).app M
    have h := deltaAlgebraFrobeniusStageResidue_homology_isZero
      D E j d k hD hj hzero hFF (-(n : ℤ)) (by omega)
    exact h.of_iso e.symm
  exact hz.of_iso (H.mapIso (deltaAlgebraPerfectionModuleColimitIso E j)).symm

/-- 実δ完全化の同じ標準導来還元は、全負次数でホモロジーが消える。 -/
theorem deltaAlgebraPerfectionResidue_negativeHomology_isZero
    (hD : D.IsPerfect) (hj : D.IsDeltaHom E j)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj))
    (n : ℕ) (hn : 0 < n) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) (-(n : ℤ))).obj (Y∞).obj) := by
  let e := (DerivedCategory.homologyFunctor (ModuleCat Q₀) (-(n : ℤ))).mapIso
      (boundedAboveDerivedBaseChangeModuleIso q₀ M∞) ≪≫
    (derivedModuleBaseChangeHomologyIso q₀ n).app M∞
  exact (deltaAlgebraPerfectionResidueTor_isZero D E j d hD hj hzero hFF n hn).of_iso e

end SerrePositivity.BhattScholze
