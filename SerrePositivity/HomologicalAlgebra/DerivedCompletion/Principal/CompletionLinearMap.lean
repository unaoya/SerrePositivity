module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 主完備化への係数線形写像の延長

## 概要
二つの代数の間の係数線形写像を、自然数 p による主完備化へ延長する。

## 方針
完備化の列表示に線形写像を項ごとに適用する。

## 規約
写像に乗法性は仮定しない。

## 使われ方
完備多項式と完備自由分冪代数の偏微分。
-/

public noncomputable section

open CategoryTheory

universe u

namespace SerrePositivity.DerivedCompletion

variable (k : Type u) [CommRing k] (p : ℕ)

/-- p による主完備化。元の基底環からの代数構造を用いる。 -/
abbrev CompletedRing (A : Type u) [CommRing A] := principalCompletionRingCat p (CommRingCat.of A)

instance completedRingAlgebra (A : Type u) [CommRing A] [Algebra k A] :
    Algebra k (CompletedRing p A) :=
  ((principalCompletionRingCatUnit p (CommRingCat.of A)).hom.comp (algebraMap k A)).toAlgebra

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]

private abbrev relation (A : Type u) [CommRing A] [Algebra k A] :=
  (LinearMap.range (principalReflectionRelation A (p : A))).restrictScalars k

private def seqMap (f : A →ₗ[k] B) : (ℕ → A) →ₗ[k] ℕ → B :=
  LinearMap.pi fun i => f.comp (LinearMap.proj i)

private theorem seqMap_relation (f : A →ₗ[k] B) (x : ℕ → A) :
    seqMap k f (principalReflectionRelation A (p : A) x) =
      principalReflectionRelation B (p : B) (seqMap k f x) := by
  funext n
  change f (sequenceShiftRight A x n - (p : A) * x n) =
    sequenceShiftRight B (seqMap k f x) n - (p : B) * f (x n)
  rw [map_sub, ← nsmul_eq_mul, ← nsmul_eq_mul, map_nsmul]
  congr 1
  cases n
  · exact map_zero f
  · rfl

private def reflectionLinearMap (f : A →ₗ[k] B) :
    PrincipalReflectionModule A (p : A) →ₗ[k] PrincipalReflectionModule B (p : B) :=
  (relation k p A).liftQ ((principalReflectionMk B (p : B)).restrictScalars k ∘ₗ
    seqMap k f) (by
      rintro _ ⟨x, rfl⟩
      change principalReflectionMk B (p : B) (seqMap k f (principalReflectionRelation A (p : A) x)) = 0
      rw [seqMap_relation]
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩)

private theorem reflectionLinearMap_mk (f : A →ₗ[k] B) (x : ℕ → A) :
    reflectionLinearMap k p f (principalReflectionMk A (p : A) x) =
      principalReflectionMk B (p : B) (seqMap k f x) := rfl

private def completionEquiv (A : Type u) [CommRing A] [Algebra k A] :
    CompletedRing p A ≃ₗ[k] PrincipalReflectionModule A (p : A) := by
  let e := principalCompletionH0Equiv A (p : A)
  refine { __ := e.toAddEquiv, map_smul' := fun c x => ?_ }
  change e (c • x) = c • e x
  let x' : PrincipalCompletionH0 A (p : A) := x
  have h₁ : c • x = (algebraMap k (CompletedRing p A) c) * x := Algebra.smul_def c x
  have h₂ := e.map_smul (algebraMap k A c) x'
  have h₃ : (algebraMap k (CompletedRing p A) c) * x =
      (algebraMap k A c) • x' := by
    let := principalCompletionCommRing A (p : A)
    let := principalCompletionAlgebra A (p : A)
    exact (Algebra.smul_def (algebraMap k A c) x').symm
  exact (congrArg (fun y : CompletedRing p A => e y) (h₁.trans h₃)).trans
    (h₂.trans (algebraMap_smul _ _ _))

private theorem completionEquiv_apply (A : Type u) [CommRing A] [Algebra k A]
    (x : CompletedRing p A) :
    completionEquiv k p A x = principalCompletionH0Equiv A (p : A) x := rfl

/-- 主完備化に誘導される係数線形写像。 -/
def principalCompletionLinearMap (f : A →ₗ[k] B) : CompletedRing p A →ₗ[k] CompletedRing p B :=
  (completionEquiv k p B).symm.toLinearMap ∘ₗ reflectionLinearMap k p f ∘ₗ
    (completionEquiv k p A).toLinearMap

/-- 延長された線形写像は完備化単位と可換。 -/
theorem principalCompletionLinearMap_unit (f : A →ₗ[k] B) (x : A) :
    principalCompletionLinearMap k p f (principalCompletionRingCatUnit p (CommRingCat.of A) x) =
      principalCompletionRingCatUnit p (CommRingCat.of B) (f x) := by
  apply (completionEquiv k p B).injective
  change (completionEquiv k p B) ((completionEquiv k p B).symm
    (reflectionLinearMap k p f ((completionEquiv k p A)
      (principalCompletionRingCatUnit p (CommRingCat.of A) x)))) =
    (completionEquiv k p B) (principalCompletionRingCatUnit p (CommRingCat.of B) (f x))
  rw [LinearEquiv.apply_symm_apply]
  rw [completionEquiv_apply k p A, completionEquiv_apply k p B]
  change reflectionLinearMap k p f
    (principalCompletionH0Equiv A (p : A) (principalCompletionUnitRingHom A (p : A) x)) =
    principalCompletionH0Equiv B (p : B) (principalCompletionUnitRingHom B (p : B) (f x))
  simp only [principalCompletionUnitRingHom_apply, principalCompletionH0Equiv_unit,
    reflectionLinearMap_mk]
  apply congrArg (principalReflectionMk B (p : B))
  funext n
  cases n
  · rfl
  · exact map_zero f

/-- 線形写像の完備化は合成を保つ。 -/
theorem principalCompletionLinearMap_comp (f : B →ₗ[k] C) (g : A →ₗ[k] B) :
    principalCompletionLinearMap k p (f.comp g) =
      (principalCompletionLinearMap k p f).comp (principalCompletionLinearMap k p g) := by
  ext x
  let e := completionEquiv k p A
  obtain ⟨z, hz⟩ := Submodule.mkQ_surjective (principalReflectionRelation A (p : A)).range (e x)
  have hx : x = e.symm (principalReflectionMk A (p : A) z) := by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    exact hz.symm
  rw [hx]
  simp only [principalCompletionLinearMap, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, e, LinearEquiv.apply_symm_apply, reflectionLinearMap_mk]
  rfl

private def completedRepresentative (x : ℕ → A) : CompletedRing p A :=
  (completionEquiv k p A).symm (principalReflectionMk A (p : A) x)

private theorem completedRepresentative_step (x : ℕ → A) :
    completedRepresentative k p x =
      principalCompletionRingCatUnit p (CommRingCat.of A) (x 0) +
        p • completedRepresentative k p (sequenceTail A x) := by
  apply (completionEquiv k p A).injective
  simp only [completedRepresentative, LinearEquiv.apply_symm_apply, map_add, map_nsmul]
  rw [principalReflectionMk_decomposition, Nat.cast_smul_eq_nsmul]
  congr 1
  rw [completionEquiv_apply k p A]
  change x 0 • principalReflectionUnit A (p : A) =
    principalCompletionH0Equiv A (p : A) (principalCompletionUnitRingHom A (p : A) (x 0))
  simp only [principalCompletionUnitRingHom_apply, principalCompletionH0Equiv_unit,
    principalReflectionUnit, ← map_smul, ← map_smul, smul_eq_mul, mul_one]

/-- 主完備加群への係数線形写像は完備化単位上の値で決まる。 -/
theorem principalCompletionLinearMap_ext {M : Type u} [AddCommGroup M] [Module k M]
    (hM : IsModuleComplete k (p : k) (ModuleCat.of k M)) {f g : CompletedRing p A →ₗ[k] M}
    (h : ∀ x : A, f (principalCompletionRingCatUnit p (CommRingCat.of A) x) =
      g (principalCompletionRingCatUnit p (CommRingCat.of A) x)) : f = g := by
  apply sub_eq_zero.mp
  let F := f - g
  have hF (x : A) : F (principalCompletionRingCatUnit p (CommRingCat.of A) x) = 0 :=
    sub_eq_zero.mpr (h x)
  apply LinearMap.ext
  intro z
  let e := completionEquiv k p A
  obtain ⟨x, hx⟩ := Submodule.mkQ_surjective (principalReflectionRelation A (p : A)).range (e z)
  have hz : z = completedRepresentative k p x := by
    apply e.injective
    exact hx.symm.trans (e.apply_symm_apply _).symm
  rw [hz]
  let y : ℕ → M := fun n => F (completedRepresentative k p (fun j => x (n + j)))
  have hy : adicRecurrenceMap (p : k) y = 0 := by
    funext n
    have ht : sequenceTail A (fun j => x (n + j)) = (fun j => x ((n + 1) + j)) := by
      funext j
      change x (n + (j + 1)) = x ((n + 1) + j)
      congr 1
      omega
    have hs := congrArg F (completedRepresentative_step k p (fun j => x (n + j)))
    rw [ht, map_add, map_nsmul, hF, zero_add] at hs
    change y n - (p : k) • y (n + 1) = 0
    rw [Nat.cast_smul_eq_nsmul]
    exact sub_eq_zero.mpr hs
  have he := ((isModuleComplete_iff_recurrence_bijective k (p : k) (ModuleCat.of k M)).mp hM).injective
    (hy.trans (map_zero _).symm)
  change F (completedRepresentative k p x) = 0
  simpa [y] using congrFun he 0

/-- 主完備化は元の係数環上の加群としても主完備。 -/
theorem completedRing_isModuleComplete :
    IsModuleComplete k (p : k) (ModuleCat.of k (CompletedRing p A)) := by
  let x : Type u := CompletedRing p A
  letI : Algebra A x := principalCompletionAlgebra A (p : A)
  letI : IsScalarTower k A x := IsScalarTower.of_algebraMap_eq' rfl
  exact (isModuleComplete_algebraMap_iff k A (p : k) x).mp (by
    rw [map_natCast]
    rw [isModuleComplete_iff_recurrence_bijective]
    exact (isModuleComplete_iff_recurrence_bijective A (p : A)
      (PrincipalCompletionH0 A (p : A))).mp (principalCompletionH0_isModuleComplete A (p : A)))

end SerrePositivity.DerivedCompletion
