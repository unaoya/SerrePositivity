module
public import SerrePositivity.DifferentialGraded.Complexes.Cells
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # diskの二段sphere filtration

上の次数n+1のsphereを部分複体とし、商は次数nのsphere。
次数付きsection/retractionにはchain map条件を課さない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

def complexDiskToSphere (n : ℤ) : complexDisk A n ⟶ complexSphere A n :=
  mkHomToSingle (complexDiskX₀ A n).hom (by
    intro i _
    rw [double_d_eq_zero₁ _ _ i n (by omega), zero_comp])

lemma complexDiskToSphere_f (n : ℤ) :
    (complexDiskToSphere A n).f n =
      (complexDiskX₀ A n).hom ≫ (singleObjXSelf (.up ℤ) n (𝟙_ (ModuleCat A))).inv :=
  mkHomToSingle_f _ _

lemma complexDiskToSphere_f_eq_zero (n k : ℤ) (hk : k ≠ n) :
    (complexDiskToSphere A n).f k = 0 :=
  (isZero_single_obj_X (.up ℤ) n (𝟙_ (ModuleCat A)) k hk).eq_of_tgt _ _

lemma complexSphereToDisk_f (n : ℤ) :
    (complexSphereToDisk A n).f (n + 1) =
      (singleObjXSelf (.up ℤ) (n + 1) (𝟙_ (ModuleCat A))).hom ≫ (complexDiskX₁ A n).inv :=
  mkHomFromSingle_f _ _

lemma complexSphereToDisk_f_eq_zero (n k : ℤ) (hk : k ≠ n + 1) :
    (complexSphereToDisk A n).f k = 0 :=
  (isZero_single_obj_X (.up ℤ) (n + 1) (𝟙_ (ModuleCat A)) k hk).eq_of_src _ _

lemma complexSphereToDiskToSphere (n : ℤ) :
    complexSphereToDisk A n ≫ complexDiskToSphere A n = 0 := by
  apply from_single_hom_ext
  simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f,
    complexDiskToSphere_f_eq_zero A n (n + 1) (by omega), comp_zero]

def complexDiskGradedRetraction (n : ℤ) :
    Homogeneous (complexDisk A n) (complexSphere A (n + 1)) 0 :=
  Cochain.single ((complexDiskX₁ A n).hom ≫
    (singleObjXSelf (.up ℤ) (n + 1) (𝟙_ (ModuleCat A))).inv) 0

def complexDiskGradedSection (n : ℤ) :
    Homogeneous (complexSphere A n) (complexDisk A n) 0 :=
  Cochain.single ((singleObjXSelf (.up ℤ) n (𝟙_ (ModuleCat A))).hom ≫
    (complexDiskX₀ A n).inv) 0

lemma complexDiskGraded_inclusion_retraction (n k : ℤ) :
    (complexSphereToDisk A n).f k ≫ (complexDiskGradedRetraction A n).v k k (add_zero k) = 𝟙 _ := by
  by_cases hk : k = n + 1
  · subst k
    simp only [complexSphereToDisk_f, complexDiskGradedRetraction, Cochain.single_v,
      Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
  · exact (isZero_single_obj_X (.up ℤ) (n + 1) (𝟙_ (ModuleCat A)) k hk).eq_of_src _ _

lemma complexDiskGraded_section_projection (n k : ℤ) :
    (complexDiskGradedSection A n).v k k (add_zero k) ≫ (complexDiskToSphere A n).f k = 𝟙 _ := by
  by_cases hk : k = n
  · subst k
    simp only [complexDiskToSphere_f, complexDiskGradedSection, Cochain.single_v,
      Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
  · exact (isZero_single_obj_X (.up ℤ) n (𝟙_ (ModuleCat A)) k hk).eq_of_src _ _

lemma complexDiskGraded_section_retraction (n k : ℤ) :
    (complexDiskGradedSection A n).v k k (add_zero k) ≫
      (complexDiskGradedRetraction A n).v k k (add_zero k) = 0 := by
  by_cases hk : k = n
  · subst k
    rw [complexDiskGradedRetraction, Cochain.single_v_eq_zero _ 0 n n (add_zero n) (by omega),
      comp_zero]
  · rw [complexDiskGradedSection, Cochain.single_v_eq_zero _ 0 k k (add_zero k) hk, zero_comp]

lemma complexDiskGraded_decomposition (n k : ℤ) :
    (complexDiskGradedRetraction A n).v k k (add_zero k) ≫ (complexSphereToDisk A n).f k +
      (complexDiskToSphere A n).f k ≫ (complexDiskGradedSection A n).v k k (add_zero k) = 𝟙 _ := by
  by_cases h₀ : k = n
  · subst k
    rw [complexDiskGradedRetraction, Cochain.single_v_eq_zero _ 0 n n (add_zero n) (by omega)]
    simp only [zero_comp, zero_add, complexDiskToSphere_f, complexDiskGradedSection,
      Cochain.single_v, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
  · by_cases h₁ : k = n + 1
    · subst k
      rw [complexDiskToSphere_f_eq_zero A n (n + 1) (by omega)]
      simp only [zero_comp, add_zero, complexDiskGradedRetraction, Cochain.single_v,
        complexSphereToDisk_f, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
    · exact (isZero_double_X _ _ k h₀ h₁).eq_of_src _ _

def complexDiskSphereShortComplex (n : ℤ) : ShortComplex (Complex A) :=
  ShortComplex.mk (complexSphereToDisk A n) (complexDiskToSphere A n)
    (complexSphereToDiskToSphere A n)

/-- 各次数でのMathlib標準の分裂データ。 -/
def complexDiskSphereSplitting (n k : ℤ) :
    ((complexDiskSphereShortComplex A n).map
      (HomologicalComplex.eval (ModuleCat A) (.up ℤ) k)).Splitting where
  r := (complexDiskGradedRetraction A n).v k k (add_zero k)
  s := (complexDiskGradedSection A n).v k k (add_zero k)
  f_r := complexDiskGraded_inclusion_retraction A n k
  s_g := complexDiskGraded_section_projection A n k
  id := complexDiskGraded_decomposition A n k

lemma complexDiskSphereShortExact (n k : ℤ) :
    ((complexDiskSphereShortComplex A n).map
      (HomologicalComplex.eval (ModuleCat A) (.up ℤ) k)).ShortExact :=
  (complexDiskSphereSplitting A n k).shortExact

lemma complexDiskGraded_inclusion_retraction_cochain (n : ℤ) :
    (Cochain.ofHom (complexSphereToDisk A n)).comp (complexDiskGradedRetraction A n)
      (zero_add 0) = Cochain.ofHom (𝟙 _) := by
  apply Cochain.ext₀
  intro k
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, Cochain.ofHom_v, HomologicalComplex.id_f]
  exact complexDiskGraded_inclusion_retraction A n k

lemma complexDiskGraded_section_projection_cochain (n : ℤ) :
    (complexDiskGradedSection A n).comp (Cochain.ofHom (complexDiskToSphere A n))
      (zero_add 0) = Cochain.ofHom (𝟙 _) := by
  apply Cochain.ext₀
  intro k
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, Cochain.ofHom_v, HomologicalComplex.id_f]
  exact complexDiskGraded_section_projection A n k

lemma complexDiskGraded_section_retraction_cochain (n : ℤ) :
    (complexDiskGradedSection A n).comp (complexDiskGradedRetraction A n) (zero_add 0) = 0 := by
  apply Cochain.ext₀
  intro k
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_v]
  exact complexDiskGraded_section_retraction A n k

lemma complexDiskGraded_decomposition_cochain (n : ℤ) :
    (complexDiskGradedRetraction A n).comp (Cochain.ofHom (complexSphereToDisk A n)) (zero_add 0) +
      (Cochain.ofHom (complexDiskToSphere A n)).comp (complexDiskGradedSection A n) (zero_add 0) =
        Cochain.ofHom (𝟙 _) := by
  apply Cochain.ext₀
  intro k
  rw [Cochain.add_v, Cochain.comp_zero_cochain_v, Cochain.comp_zero_cochain_v,
    Cochain.ofHom_v, Cochain.ofHom_v, Cochain.ofHom_v, HomologicalComplex.id_f]
  exact complexDiskGraded_decomposition A n k

end SerrePositivity.DifferentialGraded
