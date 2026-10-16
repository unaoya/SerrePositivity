module

public import SerrePositivity.BhattScholze.DeltaRootSourcePowerResidueDiscrete
public import SerrePositivity.CommutativeAlgebra.CompletelyFaithfullyFlatPowers

/-! # 実冪剰余H0の通常剰余比較と忠実平坦性 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (d : A) (b : σ → A) (n : ℕ) (hn : 0 < n)
variable (hpA : Function.Injective (fun x : A => (p : A) * x))
  (hd : IsSMulRegular A d) (v : Aˣ) (hv : (v : A) = D.delta d)
local notation "Tₙ" => A ⧸ Ideal.span (Set.insert (p : A) (Set.singleton (d ^ n)))
local notation "Kₙ" => prismaticPowerResidueIdeal (p : A) d n
local notation "Y₀" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange
    (Ideal.Quotient.mk (Ideal.span (Set.insert (p : A) (Set.singleton (d ^ n))))))
  (DeltaRootSourceIteratedPDCompletion D d b)

local notation "Sₙ" => Tₙ ⧸ Kₙ
local notation "Hₙ" => (id (α := ModuleCat Tₙ) (CategoryTheory.Functor.obj
  (DerivedCategory.homologyFunctor (ModuleCat Tₙ) 0)
  (CategoryTheory.Functor.obj DerivedCategory.Minus.ι Y₀)))
local notation "W₀" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk Kₙ)) Y₀

include hn hpA hd v hv in
/-- 実冪剰余と、その実H0の次数零対象との正規化同型。 -/
def deltaRootSourcePowerResidueSingleIso :
    Y₀ ≅ boundedAboveDerivedSingleFunctor.obj Hₙ := by
  obtain ⟨hGE, hLE, _⟩ := deltaRootSourcePowerResidue_pure_flat D d b n hn hpA hd v hv
  let := hGE
  let := hLE
  exact ObjectProperty.isoMk _ (normalizedPureHomologyIso (Y₀).obj 0)

include hn hpA hd v hv in
/-- 標準冪零商の実H0を、元の実H0の通常の係数拡大と比較する。 -/
def deltaRootSourcePowerResidueReductionH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat Sₙ) 0).obj (W₀).obj ≅
      (ModuleCat.extendScalars (Ideal.Quotient.mk Kₙ)).obj Hₙ :=
  (DerivedCategory.homologyFunctor (ModuleCat Sₙ) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk Kₙ)).mapIso
          (deltaRootSourcePowerResidueSingleIso D d b n hn hpA hd v hv))) ≪≫
    (boundedAboveDerivedBaseChangeModuleH0Iso (Ideal.Quotient.mk Kₙ)).app Hₙ

include hn hpA hd v hv in
/-- 通常の標準剰余テンソルも忠実平坦である。 -/
theorem deltaRootSourcePowerResidueH0_residueTensor_faithfullyFlat :
    Module.FaithfullyFlat Sₙ (Sₙ ⊗[Tₙ] Hₙ) := by
  have := deltaRootSourceCanonicalPowerResidueH0_faithfullyFlat D d b n hn hpA hd v hv
  let e := (deltaRootSourcePowerResidueReductionH0Iso D d b n hn hpA hd v hv).toLinearEquiv
  let eQ := (quotientScalarExtensionEquiv Kₙ Hₙ).trans
    (quotientTensorReductionEquiv Kₙ Hₙ).symm
  exact Module.FaithfullyFlat.of_linearEquiv Sₙ _ (e.trans eQ).symm

include hn hpA hd v hv in
/-- dの冪が零の実係数環上で、実H0自体が通常の忠実平坦加群となる。 -/
theorem deltaRootSourcePowerResidueH0_faithfullyFlat :
    Module.FaithfullyFlat Tₙ Hₙ := by
  have hF := deltaRootSourcePowerResidueH0_flat D d b n hn hpA hd v hv
  have hFF := deltaRootSourcePowerResidueH0_residueTensor_faithfullyFlat D d b n hn hpA hd v hv
  dsimp only [prismaticPowerResidueIdeal] at hFF
  let := hFF
  apply (Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality Tₙ Hₙ).mpr
  refine ⟨hF, ?_⟩
  intro N _ _ hTensor
  apply subsingleton_of_power_torsion_of_residueTensor
    (Ideal.Quotient.mk (Ideal.span (Set.insert (p : A) (Set.singleton (d ^ n)))) d)
    Hₙ n N ?_ hTensor
  intro x
  have hz :
      (Ideal.Quotient.mk (Ideal.span (Set.insert (p : A) (Set.singleton (d ^ n)))) d) ^ n = 0 := by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  rw [hz, zero_smul]

end SerrePositivity.BhattScholze
