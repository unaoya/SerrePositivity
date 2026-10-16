module
public import SerrePositivity.DifferentialGraded.Quotient.Paths
public import SerrePositivity.DifferentialGraded.Complexes.RightTripleCochainExt

/-! # 標準ε生成元上の評価による次数0 cochainの判定 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

lemma epsilon_generator_span (e : (epsilonComplex A).X (-1)) :
    e = ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).hom e) •
      ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A)) := by
  calc
    e = (singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv
        ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).hom e) := by
      change e = ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).hom ≫
        (singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv) e
      rw [Iso.hom_inv_id]
      rfl
    _ = _ := by rw [← map_smul]; simp only [smul_eq_mul, mul_one]

lemma epsilonMiddleCochain_ext₀ {K P T : Complex A}
    (f g : Cochain (K ⊗ (epsilonComplex A ⊗ P)) T 0)
    (h : ∀ (i j n : ℤ) (hn : i + ((-1) + j) = n) (x : K.X i) (y : P.X j),
      f.v n n (add_zero n) (ιTensorObj K (epsilonComplex A ⊗ P) i ((-1) + j) n hn
        (x ⊗ₜ[A] ιTensorObj (epsilonComplex A) P (-1) j ((-1) + j) rfl
          ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] y))) =
      g.v n n (add_zero n) (ιTensorObj K (epsilonComplex A ⊗ P) i ((-1) + j) n hn
        (x ⊗ₜ[A] ιTensorObj (epsilonComplex A) P (-1) j ((-1) + j) rfl
          ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] y)))) :
    f = g := by
  apply rightTripleCochain_ext₀
  intro i k j n hn x e y
  by_cases hk : k = -1
  · subst k
    rw [epsilon_generator_span A e]
    simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul]
    rw [h i j n hn x y]
  · let := ModuleCat.subsingleton_of_isZero
      (isZero_single_obj_X (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A)) k hk)
    have he : e = 0 := Subsingleton.elim _ _
    rw [he]
    simp only [TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero]

end SerrePositivity.DifferentialGraded.DGQuotient
