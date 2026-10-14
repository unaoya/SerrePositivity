module

public import SerrePositivity.PerfectComplex.CubicActionProjector

/-! # Lifting cubic eigenvectors to Fourier projector images -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Category Limits Preadditive
variable {R : Type u} [CommRing R]
namespace CochainCubicAction
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ} [Invertible (3 : R)]

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

/-- A chain eigenvector factors through the matching Fourier projector image. -/
def eigenvectorLift (τ : CochainCubicAction K) (a : R) (ha : a ^ 3 = 1)
    (f : L ⟶ K) (hf : f ≫ τ.map = a • f) : L ⟶ (τ.projector a ha).image :=
  equalizer.lift f (by
    rw [comp_id]
    exact (τ.eigenvector_comp_projectorMap a ha f hf).symm)

@[reassoc]
lemma eigenvectorLift_inclusion (τ : CochainCubicAction K) (a : R) (ha : a ^ 3 = 1)
    (f : L ⟶ K) (hf : f ≫ τ.map = a • f) :
    τ.eigenvectorLift a ha f hf ≫ (τ.projector a ha).inclusion = f :=
  equalizer.lift_ι _ _

end CochainCubicAction
end SerrePositivity
