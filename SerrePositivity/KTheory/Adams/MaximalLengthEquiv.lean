module

public import SerrePositivity.KTheory.Adams.MaximalLengthEvaluation

/-! # The local-length isomorphism for finite maximal support -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
namespace Adams
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (W : TopologicalSpace.Closeds (PrimeSpectrum R))
variable (hw : ∀ p ∈ W, p.asIdeal.IsMaximal)
variable [Fintype {p : PrimeSpectrum R // p ∈ W}]

def residueLinearCombination : ({p : PrimeSpectrum R // p ∈ W} → ℤ) →+ G0WithSupport W where
  toFun z := ∑ p, z p •
    G0WithSupport.mk (supportedResidueModule W p.val (hw p.val p.property) p.property)
  map_zero' := by simp
  map_add' z z' := by simp only [Pi.add_apply, add_zsmul, Finset.sum_add_distrib]

omit [Fintype {p : PrimeSpectrum R // p ∈ W}] in
open Classical in
lemma maximalLengthEvaluation_residue (p : {p : PrimeSpectrum R // p ∈ W}) :
    maximalLengthEvaluation W hw
        (G0WithSupport.mk (supportedResidueModule W p.val (hw p.val p.property) p.property)) =
      Pi.single p 1 := by
  funext q
  rw [maximalLengthEvaluation_apply, localLengthMap_residue]
  simp only [Pi.single_apply]
  by_cases he : p = q
  · subst q
    simp
  · have hv : q.val ≠ p.val := fun h => he (Subtype.ext h.symm)
    simp [hv, Ne.symm he]

omit [IsNoetherianRing R] in
open Classical in
@[simp]
lemma residueLinearCombination_single (p : {p : PrimeSpectrum R // p ∈ W}) :
    residueLinearCombination W hw (Pi.single p 1) =
      G0WithSupport.mk (supportedResidueModule W p.val (hw p.val p.property) p.property) := by
  simp [residueLinearCombination, Pi.single_apply]

lemma residueLinearCombination_evaluation (x : G0WithSupport W) :
    residueLinearCombination W hw (maximalLengthEvaluation W hw x) = x := by
  classical
  have he : (residueLinearCombination W hw).comp (maximalLengthEvaluation W hw) =
      AddMonoidHom.id (G0WithSupport W) := by
    apply residue_hom_ext W hw
    intro p hm hp
    change residueLinearCombination W hw
      (maximalLengthEvaluation W hw (G0WithSupport.mk (supportedResidueModule W p hm hp))) = _
    rw [maximalLengthEvaluation_residue W hw ⟨p, hp⟩, residueLinearCombination_single]
    rfl
  exact DFunLike.congr_fun he x

lemma maximalLengthEvaluation_combination (z : {p : PrimeSpectrum R // p ∈ W} → ℤ) :
    maximalLengthEvaluation W hw (residueLinearCombination W hw z) = z := by
  classical
  funext q
  change localLengthMap W hw q.val
    (∑ p, z p • G0WithSupport.mk
      (supportedResidueModule W p.val (hw p.val p.property) p.property)) = z q
  rw [map_sum]
  simp only [map_zsmul, localLengthMap_residue]
  simp

/-- A supported module's local lengths give the coordinates in the residue basis. -/
def maximalLengthEquiv : G0WithSupport W ≃+ ({p : PrimeSpectrum R // p ∈ W} → ℤ) where
  toFun := maximalLengthEvaluation W hw
  invFun := residueLinearCombination W hw
  left_inv := residueLinearCombination_evaluation W hw
  right_inv := maximalLengthEvaluation_combination W hw
  map_add' := (maximalLengthEvaluation W hw).map_add

lemma eq_sum_localLengthMap (x : G0WithSupport W) :
    x = ∑ p : {p : PrimeSpectrum R // p ∈ W}, localLengthMap W hw p.val x •
      G0WithSupport.mk (supportedResidueModule W p.val (hw p.val p.property) p.property) :=
  (residueLinearCombination_evaluation W hw x).symm

variable {B : Type u} [CommRing B] [Algebra R B]
variable {Z : TopologicalSpace.Closeds (PrimeSpectrum R)} {c : ℕ}
variable [IsLocalization (heightStratumComplement Z c) B]

/-- The least-height localization admits the local-length coordinate isomorphism. -/
def HeightAtLeast.semilocalLengthEquiv (h : HeightAtLeast Z c) :
    G0WithSupport (supportPullback (algebraMap R B) Z) ≃+
      ({q : PrimeSpectrum B // q ∈ supportPullback (algebraMap R B) Z} → ℤ) := by
  let := IsLocalization.isNoetherianRing (heightStratumComplement Z c) B
    (inferInstance : IsNoetherianRing R)
  have hf : (supportPullback (algebraMap R B) Z : Set (PrimeSpectrum B)).Finite :=
    h.finite_localized_maximal_points.subset
      (fun q hq => (h.mem_pullback_iff_isMax q).mp hq)
  letI := hf.fintype
  exact maximalLengthEquiv _ (fun q hq => (h.mem_pullback_iff_isMaximal q).mp hq)

end Adams
end SerrePositivity
