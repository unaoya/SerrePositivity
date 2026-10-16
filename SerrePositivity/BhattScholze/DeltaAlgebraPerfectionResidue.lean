module

public import SerrePositivity.BhattScholze.DeltaAlgebraPerfectionResidueFaithful
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete

/-! # 実δ完全化の標準還元の次数零比較 -/

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
/-- 同じ実標準係数射について、既存augmentation判定へのTor入力を供給する。 -/
theorem deltaAlgebraPerfectionResidue_scalarExtensionTorVanishing
    (hD : D.IsPerfect) (hj : D.IsDeltaHom E j)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj)) :
    scalarExtensionTorVanishing q₀ M∞ := by
  apply (derivedModuleBaseChange_negative_homology_vanishes_iff q₀ M∞).mp
  intro n hn
  let e := (DerivedCategory.homologyFunctor (ModuleCat Q₀) (-(n : ℤ))).mapIso
    (boundedAboveDerivedBaseChangeModuleIso q₀ M∞)
  exact (deltaAlgebraPerfectionResidue_negativeHomology_isZero
    D E j d hD hj hzero hFF n hn).of_iso e.symm

/-- 実δ完全化の標準還元は、既存標準augmentationにより実剰余テンソルのsingleと同型。 -/
def deltaAlgebraPerfectionResidueAugmentationIso
    (hD : D.IsPerfect) (hj : D.IsDeltaHom E j)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj)) :
    Y∞ ≅ boundedAboveDerivedSingleFunctor.obj ((ModuleCat.extendScalars q₀).obj M∞) :=
  boundedAboveDerivedBaseChangeModuleAugmentationIso q₀ M∞
    (deltaAlgebraPerfectionResidue_scalarExtensionTorVanishing D E j d hD hj hzero hFF)

/-- 実δ完全化の同じ標準導来還元の、全非零次数ホモロジー消滅。 -/
theorem deltaAlgebraPerfectionResidue_homology_isZero
    (hD : D.IsPerfect) (hj : D.IsDeltaHom E j)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj))
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y∞).obj) := by
  let e := (DerivedCategory.homologyFunctor (ModuleCat Q₀) i).mapIso
    (DerivedCategory.Minus.ι.mapIso
      (deltaAlgebraPerfectionResidueAugmentationIso D E j d hD hj hzero hFF))
  exact (derivedSingleHomology_isZero ((ModuleCat.extendScalars q₀).obj M∞) i hi).of_iso e

end SerrePositivity.BhattScholze
