module
public import SerrePositivity.DifferentialGraded.Complexes.Cells
public import SerrePositivity.DifferentialGraded.Complexes.RightTripleCochainExt

/-! # 任意次数sphereの標準生成元上のcochain判定 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

lemma sphere_generator_span (d : ℤ) (e : (complexSphere A d).X d) :
    e = ((singleObjXSelf (.up ℤ) d (𝟙_ (ModuleCat.{u} A))).hom e) •
      ((singleObjXSelf (.up ℤ) d (𝟙_ (ModuleCat.{u} A))).inv (1 : A)) := by
  calc
    e = (singleObjXSelf (.up ℤ) d (𝟙_ (ModuleCat.{u} A))).inv
        ((singleObjXSelf (.up ℤ) d (𝟙_ (ModuleCat.{u} A))).hom e) := by
      change e = ((singleObjXSelf (.up ℤ) d (𝟙_ (ModuleCat.{u} A))).hom ≫
        (singleObjXSelf (.up ℤ) d (𝟙_ (ModuleCat.{u} A))).inv) e
      rw [Iso.hom_inv_id]
      rfl
    _ = _ := by rw [← map_smul]; simp only [smul_eq_mul, mul_one]

lemma sphereMiddleCochain_ext₀ (d : ℤ) {K P T : Complex A}
    (f g : Cochain (K ⊗ (complexSphere A d ⊗ P)) T 0)
    (h : ∀ (i j n : ℤ) (hn : i + (d + j) = n) (x : K.X i) (y : P.X j),
      f.v n n (add_zero n) (ιTensorObj K (complexSphere A d ⊗ P) i (d + j) n hn
        (x ⊗ₜ[A] ιTensorObj (complexSphere A d) P d j (d + j) rfl
          ((singleObjXSelf (.up ℤ) d (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] y))) =
      g.v n n (add_zero n) (ιTensorObj K (complexSphere A d ⊗ P) i (d + j) n hn
        (x ⊗ₜ[A] ιTensorObj (complexSphere A d) P d j (d + j) rfl
          ((singleObjXSelf (.up ℤ) d (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] y)))) :
    f = g := by
  apply rightTripleCochain_ext₀
  intro i k j n hn x e y
  by_cases hk : k = d
  · subst k
    rw [sphere_generator_span A d e]
    simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul]
    rw [h i j n hn x y]
  · let := ModuleCat.subsingleton_of_isZero
      (isZero_single_obj_X (.up ℤ) d (𝟙_ (ModuleCat.{u} A)) k hk)
    have he : e = 0 := Subsingleton.elim _ _
    rw [he]
    simp only [TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero]

end SerrePositivity.DifferentialGraded
