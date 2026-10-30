module

public import SerrePositivity.PerfectComplex.IdempotentImagePerfect
public import SerrePositivity.HomologicalAlgebra.Complex.Basic
public import SerrePositivity.HomologicalAlgebra.Complex.Idempotent
public import SerrePositivity.PerfectComplex.CubicActionBasic
public import Mathlib.Algebra.Ring.Invertible

/-! # Fourier projectors for cubic chain actions -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Category Limits Preadditive
variable {R : Type u} [CommRing R]

namespace CochainCubicAction
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ} [Invertible (3 : R)]

/-- The projector for the eigenvalue a, written using a inverse = a squared. -/
def projectorMap (τ : CochainCubicAction K) (a : R) : K ⟶ K :=
  (⅟(3 : R)) • (𝟙 K + a ^ 2 • τ.map + a • (τ.map ≫ τ.map))

lemma projectorMap_comp_map (τ : CochainCubicAction K) (a : R) (ha : a ^ 3 = 1) :
    τ.projectorMap a ≫ τ.map = a • τ.projectorMap a := by
  have hac : a * a ^ 2 = 1 := by rw [← pow_succ', ha]
  calc
    τ.projectorMap a ≫ τ.map =
        (⅟(3 : R)) • (τ.map + a ^ 2 • (τ.map ≫ τ.map) + a • 𝟙 K) := by
      simp only [projectorMap, Linear.smul_comp, add_comp, id_comp, Category.assoc, τ.cube]
    _ = (⅟(3 : R)) • (a • (𝟙 K + a ^ 2 • τ.map + a • (τ.map ≫ τ.map))) := by
      congr 1
      simp only [smul_add, smul_smul, hac, one_smul, ← pow_two]
      abel
    _ = a • τ.projectorMap a := smul_comm _ _ _

lemma map_comp_projectorMap (τ : CochainCubicAction K) (a : R) (ha : a ^ 3 = 1) :
    τ.map ≫ τ.projectorMap a = a • τ.projectorMap a := by
  have hc : τ.map ≫ τ.projectorMap a = τ.projectorMap a ≫ τ.map := by
    simp only [projectorMap, Linear.comp_smul, Linear.smul_comp, comp_add, add_comp,
      id_comp, comp_id, Category.assoc]
  rw [hc, projectorMap_comp_map τ a ha]

lemma eigenvector_comp_projectorMap (τ : CochainCubicAction K)
    (a : R) (ha : a ^ 3 = 1) (f : L ⟶ K) (hf : f ≫ τ.map = a • f) :
    f ≫ τ.projectorMap a = f := by
  have hsq : f ≫ (τ.map ≫ τ.map) = a ^ 2 • f := by
    rw [← Category.assoc, hf, Linear.smul_comp, hf, smul_smul, ← pow_two]
  change f ≫ ((⅟(3 : R)) •
    (𝟙 K + a ^ 2 • τ.map + a • (τ.map ≫ τ.map))) = f
  rw [Linear.comp_smul, comp_add, comp_add, comp_id, Linear.comp_smul,
    Linear.comp_smul, hf, hsq]
  have hac : a * a ^ 2 = 1 := by rw [← pow_succ', ha]
  have hca : a ^ 2 * a = 1 := by rw [mul_comm, hac]
  simp only [smul_smul, hac, hca, one_smul]
  rw [smul_add, smul_add, ← add_smul, ← add_smul]
  have hi : ⅟(3 : R) + ⅟(3 : R) + ⅟(3 : R) = 1 := by
    calc
      _ = ⅟(3 : R) * 3 := by ring
      _ = 1 := invOf_mul_self _
  rw [hi, one_smul]

lemma projectorMap_idem (τ : CochainCubicAction K) (a : R) (ha : a ^ 3 = 1) :
    τ.projectorMap a ≫ τ.projectorMap a = τ.projectorMap a :=
  τ.eigenvector_comp_projectorMap a ha (τ.projectorMap a) (τ.projectorMap_comp_map a ha)

/-- Each cubic root supplies an idempotent chain map. -/
def projector (τ : CochainCubicAction K) (a : R) (ha : a ^ 3 = 1) : CochainIdempotent K :=
  ⟨τ.projectorMap a, τ.projectorMap_idem a ha⟩

@[reassoc]
lemma projectorMap_naturality {L : CochainComplex (ModuleCat.{u} R) ℤ}
    (τ : CochainCubicAction K) (σ : CochainCubicAction L) (f : K ⟶ L)
    (hf : τ.map ≫ f = f ≫ σ.map) (a : R) :
    τ.projectorMap a ≫ f = f ≫ σ.projectorMap a := by
  have hsq : (τ.map ≫ τ.map) ≫ f = f ≫ (σ.map ≫ σ.map) := by
    rw [Category.assoc, hf, ← Category.assoc, hf, Category.assoc]
  simp only [projectorMap, Linear.smul_comp, Linear.comp_smul,
    add_comp, comp_add, id_comp, comp_id, hf, hsq]

lemma projectorMap_orthogonal (τ : CochainCubicAction K) (a b : R)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab : IsUnit (a - b)) :
    τ.projectorMap a ≫ τ.projectorMap b = 0 := by
  have he : a • (τ.projectorMap a ≫ τ.projectorMap b) =
      b • (τ.projectorMap a ≫ τ.projectorMap b) := by
    calc
      _ = (τ.projectorMap a ≫ τ.map) ≫ τ.projectorMap b := by
        rw [projectorMap_comp_map τ a ha, Linear.smul_comp]
      _ = τ.projectorMap a ≫ (τ.map ≫ τ.projectorMap b) := Category.assoc _ _ _
      _ = _ := by rw [map_comp_projectorMap τ b hb, Linear.comp_smul]
  have hz : (a - b) • (τ.projectorMap a ≫ τ.projectorMap b) = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact he
  apply hab.smul_left_cancel.mp
  simpa only [smul_zero] using hz

@[reassoc]
lemma projector_inclusion_eigen (τ : CochainCubicAction K) (a : R) (ha : a ^ 3 = 1) :
    (τ.projector a ha).inclusion ≫ τ.map = a • (τ.projector a ha).inclusion := by
  calc
    _ = (τ.projector a ha).inclusion ≫ (τ.projectorMap a ≫ τ.map) := by
      rw [← Category.assoc]
      exact congrArg (fun f => f ≫ τ.map) (τ.projector a ha).inclusion_map.symm
    _ = (τ.projector a ha).inclusion ≫ (a • τ.projectorMap a) := by
      rw [projectorMap_comp_map τ a ha]
    _ = _ := by
      rw [Linear.comp_smul]
      exact congrArg (fun f => a • f) (τ.projector a ha).inclusion_map

end CochainCubicAction
end SerrePositivity
