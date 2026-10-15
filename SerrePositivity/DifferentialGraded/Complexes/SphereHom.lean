module
public import SerrePositivity.DifferentialGraded.Complexes.Cells
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # sphereからの全次数Homとacyclic性

singleからのcochainは唯一の生成元の像で決まり、Hom微分は値域の微分になる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

def complexSphereHomElementEquiv (K : Complex A) (n p : ℤ) :
    (homComplex A (complexSphere A n) K).X p ≃ K.X (n + p) :=
  (Cochain.fromSingleEquiv (X := 𝟙_ (ModuleCat A)) (K := K) (rfl : n + p = n + p)).toEquiv.trans
    (moduleElementEquiv A (K.X (n + p)))

def complexSphereHomElementLinearEquiv (K : Complex A) (n p : ℤ) :
    (homComplex A (complexSphere A n) K).X p ≃ₗ[A] K.X (n + p) where
  toEquiv := complexSphereHomElementEquiv A K n p
  map_add' z t := by
    change (Cochain.fromSingleEquiv (X := 𝟙_ (ModuleCat A)) (K := K)
      (rfl : n + p = n + p) (z + t)) (1 : A) = _
    rw [map_add]
    rfl
  map_smul' r z := by
    change (Cochain.fromSingleEquiv (X := 𝟙_ (ModuleCat A)) (K := K)
      (rfl : n + p = n + p) (r • z)) (1 : A) = _
    rw [Cochain.fromSingleEquiv_smul]
    rfl

lemma complexSphereHomElementEquiv_zero (K : Complex A) (n p : ℤ) :
    complexSphereHomElementEquiv A K n p 0 = 0 := by
  change (Cochain.fromSingleEquiv (X := 𝟙_ (ModuleCat A)) (K := K) (rfl : n + p = n + p) 0)
    (1 : A) = 0
  rw [map_zero]
  rfl

lemma complexSphereHomElementEquiv_d (K : Complex A) (n p q : ℤ)
    (z : (homComplex A (complexSphere A n) K).X p) :
    complexSphereHomElementEquiv A K n q ((homComplex A (complexSphere A n) K).d p q z) =
      K.d (n + p) (n + q) (complexSphereHomElementEquiv A K n p z) := by
  obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective z (n + p) rfl
  change (Cochain.fromSingleEquiv (X := 𝟙_ (ModuleCat A)) (K := K) (rfl : n + q = n + q)
    (δ p q (Cochain.fromSingleMk f rfl))) (1 : A) =
      K.d (n + p) (n + q)
        ((Cochain.fromSingleEquiv (X := 𝟙_ (ModuleCat A)) (K := K) rfl
          (Cochain.fromSingleMk f (rfl : n + p = n + p))) (1 : A))
  rw [Cochain.δ_fromSingleMk f (rfl : n + p = n + p) q (n + q) rfl,
    Cochain.fromSingleEquiv_fromSingleMk,
    Cochain.fromSingleEquiv_fromSingleMk]
  rfl

/-- 全整数次数でsphereからのHomはacyclic複体をacyclicに送る。 -/
lemma complexSphereHom_acyclic (K : Complex A) (n : ℤ) (hK : K.Acyclic) :
    (homComplex A (complexSphere A n) K).Acyclic := by
  intro p
  apply (HomologicalComplex.exactAt_iff' (K := homComplex A (complexSphere A n) K)
    (i := p - 1) (j := p) (k := p + 1) (by simp) (by simp)).2
  rw [ShortComplex.moduleCat_exact_iff]
  change ∀ z : (homComplex A (complexSphere A n) K).X p,
    (homComplex A (complexSphere A n) K).d p (p + 1) z = 0 →
      ∃ t : (homComplex A (complexSphere A n) K).X (p - 1),
        (homComplex A (complexSphere A n) K).d (p - 1) p t = z
  intro z hz
  have hc := congrArg (complexSphereHomElementEquiv A K n (p + 1)) hz
  rw [complexSphereHomElementEquiv_d, complexSphereHomElementEquiv_zero] at hc
  have he := (HomologicalComplex.exactAt_iff' (K := K)
    (i := n + (p - 1)) (j := n + p) (k := n + (p + 1))
      (by simp; omega) (by simp; omega)).1 (hK (n + p))
  rw [ShortComplex.moduleCat_exact_iff] at he
  change ∀ y : K.X (n + p), K.d (n + p) (n + (p + 1)) y = 0 →
    ∃ t : K.X (n + (p - 1)), K.d (n + (p - 1)) (n + p) t = y at he
  obtain ⟨t, ht⟩ := he (complexSphereHomElementEquiv A K n p z) hc
  refine ⟨(complexSphereHomElementEquiv A K n (p - 1)).symm t, ?_⟩
  apply (complexSphereHomElementEquiv A K n p).injective
  rw [complexSphereHomElementEquiv_d, Equiv.apply_symm_apply]
  exact ht

end SerrePositivity.DifferentialGraded
