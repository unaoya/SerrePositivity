module

public import SerrePositivity.EInfinity.SimplexCuts.SimplexGeneratorLinearExt
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying

/-!
# 一般単体集合と二つのχ係数の複体射の外延性

Berger–Fresse §1.2.1・§2.2.6、M14 L14/L16、報告 §387。
全整数の同じ三重斉次成分を元の語基底と全正規化単体で比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 元の二つの語基底と単体の三重斉次包含の値（BF §2.2.6）。 -/
def wordPairSimplexInput (S : SSet.{0}) {m n d e q : ℕ}
    (u : Surjection.BasisWord m d) (v : Surjection.BasisWord n e) (x : S _⦋q⦌) :
    ((Surjection.complex A m ⊗ Surjection.complex A n) ⊗ chains A S).X
      (-(d : ℤ) + -(e : ℤ) + -(q : ℤ)) :=
  ιTensorObj (Surjection.complex A m ⊗ Surjection.complex A n) (chains A S)
    (-(d : ℤ) + -(e : ℤ)) (-(q : ℤ)) (-(d : ℤ) + -(e : ℤ) + -(q : ℤ)) rfl
    (ιTensorObj (Surjection.complex A m) (Surjection.complex A n)
      (-(d : ℤ)) (-(e : ℤ)) (-(d : ℤ) + -(e : ℤ)) rfl
      ((Surjection.complexXIso A m d).inv (Surjection.basis A m d (ULift.up u)) ⊗ₜ[A]
        (Surjection.complexXIso A n e).inv (Surjection.basis A n e (ULift.up v))) ⊗ₜ[A] gen A S q x)

/-- 全整数の元の複体射は二語基底と全単体の値で決まる（BF §2.2.6）。 -/
lemma coefficient_simplex_hom_ext (S : SSet.{0}) (m n : ℕ)
    {K : Complex A} {f g : (Surjection.complex A m ⊗ Surjection.complex A n) ⊗ chains A S ⟶ K}
    (h : ∀ (d e q : ℕ) (u : Surjection.BasisWord m d) (v : Surjection.BasisWord n e) (x : S _⦋q⦌),
      f.f (-(d : ℤ) + -(e : ℤ) + -(q : ℤ)) (wordPairSimplexInput A S u v x) =
        g.f (-(d : ℤ) + -(e : ℤ) + -(q : ℤ)) (wordPairSimplexInput A S u v x)) : f = g := by
  apply triple_ext
  intro i j l z hz
  by_cases hi : 0 < i
  · apply ModuleCat.hom_ext
    apply TensorProduct.ext_threefold
    intro a b c
    simp only [Surjection.complex_eq_zero_of_positive A m i hi a,
      TensorProduct.zero_tmul, map_zero]
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, i = -(d : ℤ) := ⟨(-i).toNat, by omega⟩
  by_cases hj : 0 < j
  · apply ModuleCat.hom_ext
    apply TensorProduct.ext_threefold
    intro a b c
    simp only [Surjection.complex_eq_zero_of_positive A n j hj b,
      TensorProduct.tmul_zero, TensorProduct.zero_tmul, map_zero]
  obtain ⟨e, rfl⟩ : ∃ e : ℕ, j = -(e : ℤ) := ⟨(-j).toNat, by omega⟩
  by_cases hl : 0 < l
  · have hzero : Limits.IsZero ((chains A S).X l) := by
      apply HomologicalComplex.isZero_extend_X
      intro q
      change -(q : ℤ) ≠ l
      omega
    let _ := ModuleCat.isZero_iff_subsingleton.mp hzero
    apply ModuleCat.hom_ext
    apply TensorProduct.ext_threefold
    intro a b c
    have hc : c = 0 := Subsingleton.elim _ _
    simp only [hc, TensorProduct.tmul_zero, map_zero]
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, l = -(q : ℤ) := ⟨(-l).toNat, by omega⟩
  have he : z = -(d : ℤ) + -(e : ℤ) + -(q : ℤ) := hz.symm
  subst he
  apply ModuleCat.hom_ext
  apply coefficient_simplex_linear_ext A S m n d e q
  intro u v x
  have hx := nested_left_apply (Surjection.complex A m) (Surjection.complex A n) (chains A S)
    (-(d : ℤ)) (-(e : ℤ)) (-(q : ℤ)) (-(d : ℤ) + -(e : ℤ))
    (-(d : ℤ) + -(e : ℤ) + -(q : ℤ)) rfl rfl
    ((Surjection.complexXIso A m d).inv (Surjection.basis A m d (ULift.up u)))
    ((Surjection.complexXIso A n e).inv (Surjection.basis A n e (ULift.up v))) (gen A S q x)
  exact (congrArg (fun y => f.f _ y) hx).symm.trans
    ((h d e q u v x).trans (congrArg (fun y => g.f _ y) hx))

end SerrePositivity.EInfinity.SimplexCuts
