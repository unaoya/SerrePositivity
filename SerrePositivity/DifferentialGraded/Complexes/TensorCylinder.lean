module
public import SerrePositivity.DifferentialGraded.Complexes.Braiding
public import Mathlib.Algebra.Homology.Precylinder
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.BifunctorHomotopy

/-! # 単位複体の cylinder の tensor は任意非有界複体でホモトピー同値 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A]

/-- 単位複体の標準cylinder。 -/
abbrev dgInterval : Complex A := (𝟙_ (Complex A)).cylinder

/-- 標準cylinderの収縮を任意複体へtensorする。flatnessを要求しない。 -/
def tensorIntervalHomotopyEquiv (P : Complex A) :
    HomotopyEquiv (dgInterval A ⊗ P) ((𝟙_ (Complex A)) ⊗ P) where
  hom := cylinder.π (𝟙_ (Complex A)) ⊗ₘ 𝟙 P
  inv := cylinder.ι₀ (𝟙_ (Complex A)) ⊗ₘ 𝟙 P
  homotopyHomInvId := by
    have h := mapBifunctorMapHomotopy₁
      (cylinder.πCompι₀Homotopy (𝟙_ (Complex A)) (fun n => ⟨n - 1, by simp⟩))
      (𝟙 P) (curriedTensor (ModuleCat A)) (.up ℤ)
    change Homotopy ((cylinder.π _ ≫ cylinder.ι₀ _) ⊗ₘ 𝟙 P)
      (𝟙 (dgInterval A) ⊗ₘ 𝟙 P) at h
    rw [tensorHom_comp_tensorHom, Category.id_comp]
    simpa only [tensorHom_id, id_whiskerRight] using h
  homotopyInvHomId := Homotopy.ofEq (by
    rw [tensorHom_comp_tensorHom, cylinder.ι₀_π, Category.id_comp, tensorHom_id,
      id_whiskerRight])

lemma tensorIntervalProjection_quasiIso (P : Complex A) :
    QuasiIso ((cylinder.π (𝟙_ (Complex A)) ⊗ₘ 𝟙 P) ≫ (λ_ P).hom) := by
  have : QuasiIso (cylinder.π (𝟙_ (Complex A)) ⊗ₘ 𝟙 P) :=
    (tensorIntervalHomotopyEquiv A P).quasiIso_hom
  infer_instance

end SerrePositivity.DifferentialGraded
