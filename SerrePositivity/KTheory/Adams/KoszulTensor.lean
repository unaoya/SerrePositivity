module

public import SerrePositivity.KTheory.Adams.KoszulNormalization
public import SerrePositivity.KTheory.Adams.TensorSquareMultiplicativity

/-! # Tensor factorization of a Koszul complex by its last one-element factor -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex CochainComplex
variable {R : Type u} [CommRing R]
namespace Adams

abbrev koszulClosedSupport {n : ℕ} (x : Fin n → R) :=
  supportZeroLocus (Ideal.span (Set.range x))

lemma koszulComplex_closedSupport {n : ℕ} (x : Fin n → R) :
    HasHomologySupportOn (koszulClosedSupport x) (koszulComplex x) :=
  (isPerfectSupported_koszulComplex x).supported.homologySupport

lemma koszulClosedSupport_succ {n : ℕ} (x : Fin (n + 1) → R) :
    koszulClosedSupport x =
      oneKoszulSupport (x (Fin.last n)) ⊓ koszulClosedSupport (Fin.init x) := by
  apply SetLike.coe_injective
  ext p
  simp only [koszulClosedSupport, oneKoszulSupport, TopologicalSpace.Closeds.coe_inf,
    coe_supportZeroLocus, Set.mem_inter_iff, PrimeSpectrum.mem_zeroLocus,
    SetLike.coe_subset_coe, Ideal.span_le, Set.range_subset_iff, Set.singleton_subset_iff]
  change (∀ i, x i ∈ p.asIdeal) ↔
    (x (Fin.last n) ∈ p.asIdeal ∧ ∀ j : Fin n, x j.castSucc ∈ p.asIdeal)
  constructor
  · intro h
    exact ⟨h (Fin.last n), fun j => h j.castSucc⟩
  · intro h i
    exact Fin.lastCases h.1 (fun j => h.2 j) i

lemma oneKoszulTensorScalar_leftUnitor (a : R) (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainTensorMap (oneKoszulScalarMap a) (𝟙 P) ≫ (cochainTensorLeftUnitor P).hom =
      (cochainTensorLeftUnitor P).hom ≫ smulId a P := by
  change cochainTensorMap (a • 𝟙 cochainTensorUnit) (𝟙 P) ≫ _ = _
  rw [cochainTensorMap_smul_left]
  calc
    _ = (a • 𝟙 (cochainTensor cochainTensorUnit P)) ≫ (cochainTensorLeftUnitor P).hom :=
      congrArg (fun f => (a • f) ≫ (cochainTensorLeftUnitor P).hom)
        (cochainTensorMap_id cochainTensorUnit P)
    _ = _ := by simp [smulId, Linear.smul_comp, Linear.comp_smul]

def oneKoszulTensorConeIso (a : R) (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainTensor (oneKoszulComplex a) P ≅ mappingCone (smulId a P) :=
  cochainTensorConeLeft (oneKoszulScalarMap a) P ≪≫
    HomologicalComplex.homotopyCofiber.mapArrowIso _ _ (fun j => ⟨j - 1, by simp⟩)
      (Arrow.isoMk (cochainTensorLeftUnitor P) (cochainTensorLeftUnitor P)
        (oneKoszulTensorScalar_leftUnitor a P).symm)

/-- The recursive Koszul cone is the tensor with the last one-element Koszul factor. -/
def koszulSuccTensorIso {n : ℕ} (x : Fin (n + 1) → R) :
    cochainTensor (oneKoszulComplex (x (Fin.last n))) (koszulComplex (Fin.init x)) ≅
      koszulComplex x :=
  oneKoszulTensorConeIso (x (Fin.last n)) (koszulComplex (Fin.init x))

end Adams
end SerrePositivity
