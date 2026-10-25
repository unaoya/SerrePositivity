module

public import SerrePositivity.BhattScholze.RootedExtension.DeltaAlgebra.DeltaAlgebraPerfectionResidue
public import SerrePositivity.BhattScholze.Prism.PrismaticCoefficientCompletionReduction

/-! # 実δ完全化の逐次導来完備化の標準還元 -/

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
local notation "Cp" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)
local notation "Cd" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A d
local notation "Up" => DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)
local notation "Ud" => DerivedCompletion.boundedAboveDerivedCompletionUnit A d

/-- 同じ実δ完全化の正確なA加群を、既存の実p,d関手で逐次完備化した対象。 -/
abbrev DeltaAlgebraPerfectionIteratedPDCompletion := (Cd).obj ((Cp).obj X∞)

/-- 個別に正則なp,dについて、逐次完備化後の実還元は未完備還元と比較できる。 -/
def deltaAlgebraPerfectionCompletionReductionIso
    (hp : IsSMulRegular A (p : A)) (hd : IsSMulRegular A d) :
    (boundedAboveDerivedBaseChange q₀).obj (DeltaAlgebraPerfectionIteratedPDCompletion E j d) ≅
      Y∞ :=
  prismaticCoefficientIteratedCompletionPairIso (p : A) d hp hd X∞

/-- 還元比較は、二つの元の標準完備化単位の合成を保つ。 -/
theorem deltaAlgebraPerfectionCompletionReductionIso_unit
    (hp : IsSMulRegular A (p : A)) (hd : IsSMulRegular A d) :
    (boundedAboveDerivedBaseChange q₀).map (((Up).app X∞) ≫ (Ud).app ((Cp).obj X∞)) ≫
      (deltaAlgebraPerfectionCompletionReductionIso E j d hp hd).hom = 𝟙 _ :=
  prismaticCoefficientIteratedCompletionPairIso_unit (p : A) d hp hd X∞

/-- 実δ完全化の逐次導来完備化後の標準還元の全非零次数は零。 -/
theorem deltaAlgebraPerfectionCompletionResidue_homology_isZero
    (hD : D.IsPerfect) (hj : D.IsDeltaHom E j) (hd : IsSMulRegular A d)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj))
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj
      ((boundedAboveDerivedBaseChange q₀).obj
        (DeltaAlgebraPerfectionIteratedPDCompletion E j d)).obj) :=
  (deltaAlgebraPerfectionResidue_homology_isZero D E j d hD hj hzero hFF i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (deltaAlgebraPerfectionCompletionReductionIso E j d hD.p_mul_injective hd)))

/-- 同じ逐次完備化後の実標準還元H0は、正確なA/(p,d)上で忠実平坦。 -/
theorem deltaAlgebraPerfectionCompletionResidueH0_faithfullyFlat
    (hD : D.IsPerfect) (hj : D.IsDeltaHom E j) (hd : IsSMulRegular A d)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj)) :
    Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
        ((boundedAboveDerivedBaseChange q₀).obj
          (DeltaAlgebraPerfectionIteratedPDCompletion E j d)).obj) := by
  let M := (DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y∞).obj
  have : Module.FaithfullyFlat Q₀ M :=
    deltaAlgebraPerfectionResidueH0_faithfullyFlat D E j d hD hj hzero hFF
  let e := (DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).mapIso
    (DerivedCategory.Minus.ι.mapIso
      (deltaAlgebraPerfectionCompletionReductionIso E j d hD.p_mul_injective hd))
  exact Module.FaithfullyFlat.of_linearEquiv Q₀ M e.toLinearEquiv

end SerrePositivity.BhattScholze
