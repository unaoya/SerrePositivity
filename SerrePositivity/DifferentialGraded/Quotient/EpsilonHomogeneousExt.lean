module
public import SerrePositivity.DifferentialGraded.Quotient.EpsilonCochainExt

/-! 任意次数の cochain を標準 ε 生成元上で判定する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R]

lemma epsilonMiddleCochain_ext {K P T : Complex R} {d : ℤ}
    (f g : Cochain (K ⊗ (epsilonComplex R ⊗ P)) T d)
    (h : ∀ (i j a n : ℤ) (ha : i + ((-1) + j) = a) (hn : a + d = n)
      (x : K.X i) (y : P.X j),
      f.v a n hn (ιTensorObj K (epsilonComplex R ⊗ P) i ((-1) + j) a ha
        (x ⊗ₜ[R] ιTensorObj (epsilonComplex R) P (-1) j ((-1) + j) rfl
          ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} R))).inv (1 : R) ⊗ₜ[R] y))) =
      g.v a n hn (ιTensorObj K (epsilonComplex R ⊗ P) i ((-1) + j) a ha
        (x ⊗ₜ[R] ιTensorObj (epsilonComplex R) P (-1) j ((-1) + j) rfl
          ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} R))).inv (1 : R) ⊗ₜ[R] y)))) :
    f = g := by
  apply rightTripleCochain_ext
  intro i k j a n ha hn x e y
  by_cases hk : k = -1
  · subst k
    rw [epsilon_generator_span R e]
    simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul]
    rw [h i j a n ha hn x y]
  · let := ModuleCat.subsingleton_of_isZero
      (isZero_single_obj_X (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} R)) k hk)
    have he : e = 0 := Subsingleton.elim _ _
    rw [he]
    simp only [TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero]

end SerrePositivity.DifferentialGraded.DGQuotient
