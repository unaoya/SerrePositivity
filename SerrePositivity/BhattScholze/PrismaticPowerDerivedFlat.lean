module

public import SerrePositivity.BhattScholze.PrismaticPowerResidueCanonical
public import SerrePositivity.BhattScholze.PrismaticPowerResidueDerived
public import SerrePositivity.HomologicalAlgebra.NilpotentDerivedReduction
public import SerrePositivity.HomologicalAlgebra.DerivedPureHomology
public import SerrePositivity.CommutativeAlgebra.CompletelyFaithfullyFlatPowers

/-! # 実prism冪剰余へのG10と忠実性判定の適用 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {A : Type u} [CommRing A] (a d : A) (n : ℕ) (hn : 0 < n)
variable (X : DerivedCategory.Minus (ModuleCat.{u} A))
local notation "Q₀" => A ⧸ Ideal.span (Set.insert a (Set.singleton d))
local notation "Qₙ" => A ⧸ Ideal.span (Set.insert a (Set.singleton (d ^ n)))
local notation "q₀" => Ideal.Quotient.mk (Ideal.span (Set.insert a (Set.singleton d)))
local notation "qₙ" => Ideal.Quotient.mk (Ideal.span (Set.insert a (Set.singleton (d ^ n))))
local notation "Kₙ" => prismaticPowerResidueIdeal a d n
local notation "Sₙ" => Qₙ ⧸ Kₙ
local notation "eₙ" => prismaticPowerResidueQuotientEquiv a d n hn
local notation "Y₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q₀) X
local notation "Yₙ" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange qₙ) X
local notation "Wₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk Kₙ)) Yₙ

/-- 実冪剰余の標準冪零還元を、元の実一乗剰余への係数制限へ比較する。 -/
def prismaticPowerCanonicalReductionIso :
    Wₙ ≅ (boundedAboveDerivedRestrictScalars (eₙ).toRingHom).obj Y₀ :=
  prismaticPowerResidueCanonicalDerivedIso a d n hn Yₙ ≪≫
    (boundedAboveDerivedRestrictScalars (eₙ).toRingHom).mapIso
      (prismaticPowerResidueDerivedCompositionIso a d n hn X).symm

include hn in
/-- 元の実(a,d)還元が次数零・忠実平坦なら、実(a,dⁿ)還元もそうである。 -/
theorem prismaticPowerDerivedReduction_pure_faithfullyFlat
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj)) :
    (Yₙ).obj.IsGE 0 ∧ (Yₙ).obj.IsLE 0 ∧
      Module.FaithfullyFlat Qₙ
        ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) 0).obj (Yₙ).obj) := by
  let H₀ := (DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj
  let Hₙ := (DerivedCategory.homologyFunctor (ModuleCat Qₙ) 0).obj (Yₙ).obj
  let eH (i : ℤ) : (DerivedCategory.homologyFunctor (ModuleCat Sₙ) i).obj (Wₙ).obj ≅
      (ModuleCat.restrictScalars (eₙ).toRingHom).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj) :=
    (DerivedCategory.homologyFunctor (ModuleCat Sₙ) i).mapIso
        (DerivedCategory.Minus.ι.mapIso (prismaticPowerCanonicalReductionIso a d n hn X)) ≪≫
      (derivedRestrictScalarsHomologyIso (eₙ).toRingHom i).app (Y₀).obj
  have hWzero (i : ℤ) (hi : i ≠ 0) :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Sₙ) i).obj (Wₙ).obj) :=
    ((ModuleCat.restrictScalars (eₙ).toRingHom).map_isZero (hzero i hi)).of_iso (eH i)
  have hWFF : Module.FaithfullyFlat Sₙ
      ((DerivedCategory.homologyFunctor (ModuleCat Sₙ) 0).obj (Wₙ).obj) := by
    let := (eₙ).toRingHom.toAlgebra
    let : Module Sₙ H₀ := Module.compHom H₀ (eₙ).toRingHom
    let : IsScalarTower Sₙ Q₀ H₀ := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    let eA : Sₙ ≃ₐ[Sₙ] Q₀ := AlgEquiv.ofBijective (Algebra.ofId Sₙ Q₀) (eₙ).bijective
    have : Module.FaithfullyFlat Sₙ Q₀ :=
      Module.FaithfullyFlat.of_linearEquiv Sₙ Sₙ eA.symm.toLinearEquiv
    have : Module.FaithfullyFlat Q₀ H₀ := hFF
    have : Module.FaithfullyFlat Sₙ H₀ := Module.FaithfullyFlat.trans Sₙ Q₀ H₀
    exact Module.FaithfullyFlat.of_linearEquiv Sₙ H₀ (eH 0).toLinearEquiv
  let := hWFF
  obtain ⟨hGE, hLE, hFlat⟩ := derived_pure_flat_of_nilpotent_reduction Kₙ Yₙ hWzero
    inferInstance ⟨n, prismaticPowerResidueIdeal_pow a d n⟩
  let := hGE
  let := hLE
  let eY : Yₙ ≅ boundedAboveDerivedSingleFunctor.obj Hₙ :=
    ObjectProperty.isoMk _ (normalizedPureHomologyIso (Yₙ).obj 0)
  let eRed : (DerivedCategory.homologyFunctor (ModuleCat Sₙ) 0).obj (Wₙ).obj ≅
      (ModuleCat.extendScalars (Ideal.Quotient.mk Kₙ)).obj Hₙ :=
    (DerivedCategory.homologyFunctor (ModuleCat Sₙ) 0).mapIso
        (DerivedCategory.Minus.ι.mapIso
          ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk Kₙ)).mapIso eY)) ≪≫
      (boundedAboveDerivedBaseChangeModuleH0Iso (Ideal.Quotient.mk Kₙ)).app Hₙ
  have hTensor : Module.FaithfullyFlat Sₙ (Sₙ ⊗[Qₙ] Hₙ) := by
    let eQ := (quotientScalarExtensionEquiv Kₙ Hₙ).trans
      (quotientTensorReductionEquiv Kₙ Hₙ).symm
    exact Module.FaithfullyFlat.of_linearEquiv Sₙ _ (eRed.toLinearEquiv.trans eQ).symm
  refine ⟨hGE, hLE, ?_⟩
  dsimp only [prismaticPowerResidueIdeal] at hTensor
  let := hTensor
  apply (Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality Qₙ Hₙ).mpr
  refine ⟨hFlat, ?_⟩
  intro N _ _ hT
  apply subsingleton_of_power_torsion_of_residueTensor (qₙ d) Hₙ n N ?_ hT
  intro x
  have hz : (qₙ d) ^ n = 0 := by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  rw [hz, zero_smul]

end SerrePositivity.BhattScholze
