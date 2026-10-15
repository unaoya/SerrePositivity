module
public import SerrePositivity.DifferentialGraded.Complexes.Cells
public import SerrePositivity.DifferentialGraded.Complexes.Monoidal
public import Mathlib.Algebra.Homology.BifunctorHomotopy

/-! # コチェインdiskの次数−1の収縮 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- 上の次数n+1から下の次数nへ戻す収縮cochain。 -/
def complexDiskContractingCochain (n : ℤ) :
    Homogeneous (complexDisk A n) (complexDisk A n) (-1) :=
  Cochain.single ((complexDiskX₁ A n).hom ≫ (complexDiskX₀ A n).inv) (-1)

lemma complexDiskContracting_d (n : ℤ) :
    δ (-1) 0 (complexDiskContractingCochain A n) = Cochain.ofHom (𝟙 (complexDisk A n)) := by
  rw [complexDiskContractingCochain, Cochain.δ_single _ (-1) 0 (by omega) n (n + 1) rfl rfl]
  have hd : (complexDisk A n).d n (n + 1) = (complexDiskX₀ A n).hom ≫ (complexDiskX₁ A n).inv := by
    rw [double_d _ _ (by omega)]
    simp only [Category.id_comp]
  rw [hd]
  simp only [Int.negOnePow_zero, one_smul, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id]
  apply Cochain.ext₀
  intro k
  by_cases h₀ : k = n
  · subst k
    rw [Cochain.add_v, Cochain.single_v_eq_zero _ _ _ _ _ (by omega), Cochain.single_v,
      Cochain.ofHom_v]
    simp
  · by_cases h₁ : k = n + 1
    · subst k
      rw [Cochain.add_v, Cochain.single_v, Cochain.single_v_eq_zero _ _ _ _ _ (by omega),
        Cochain.ofHom_v]
      simp
    · exact (isZero_double_X _ _ k h₀ h₁).eq_of_src _ _

/-- diskの恒等射から零射への次数−1のホモトピー。 -/
def complexDiskContractingHomotopy (n : ℤ) : Homotopy (𝟙 (complexDisk A n)) 0 :=
  contractingHomotopy _ (complexDiskContractingCochain A n) (complexDiskContracting_d A n)

lemma complexDisk_acyclic (n : ℤ) : (complexDisk A n).Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  apply (IsZero.iff_id_eq_zero _).2
  have h := (complexDiskContractingHomotopy A n).homologyMap_eq i
  simpa only [homologyMap_id, homologyMap_zero] using h

/-- 具体的収縮は任意非有界複体とのtensorで保存される。 -/
def complexDiskTensorContractingHomotopy (n : ℤ) (P : Complex A) :
    Homotopy (𝟙 (complexDisk A n ⊗ P)) 0 := by
  have h := mapBifunctorMapHomotopy₁ (complexDiskContractingHomotopy A n)
    (𝟙 P) (curriedTensor (ModuleCat A)) (.up ℤ)
  change Homotopy (𝟙 (complexDisk A n) ⊗ₘ 𝟙 P) (0 ⊗ₘ 𝟙 P) at h
  simpa only [tensorHom_id, id_whiskerRight, MonoidalPreadditive.zero_whiskerRight] using h

lemma complexDiskTensor_acyclic (n : ℤ) (P : Complex A) : (complexDisk A n ⊗ P).Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  apply (IsZero.iff_id_eq_zero _).2
  have h := (complexDiskTensorContractingHomotopy A n P).homologyMap_eq i
  simpa only [homologyMap_id, homologyMap_zero] using h

end SerrePositivity.DifferentialGraded
