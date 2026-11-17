module

public import SerrePositivity.CommutativeAlgebra.DeRham.PolynomialCompletion
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCompletedFreeDelta
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# 元の完備多項式環のpで零化された係数への通常底変換

## 概要
pが零の係数への通常底変換では、元のp完備多項式環を通常の多項式環で計算できる。

## 方針
標準完備化単位の普遍性と元の多項式の自由性で互いに逆の代数写像を作る。

## 規約
平坦性・Noether性・ねじれの有界性は仮定しない。元の単位純テンソルの値を保つ。

## 使われ方
被覆上の元の零次・一次形式の通常係数拡大の同型と標準写像の照合。
-/

public noncomputable section
universe u
open CategoryTheory
open scoped TensorProduct
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DerivedCompletion SerrePositivity.DeRham
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (k l : Type u) [CommRing k] [CommRing l] [Algebra k l]
variable (T : Type u) [Fintype T] [DecidableEq T] (p : ℕ) (hp : (p : l) = 0)

include hp
/-- 元の完備化単位を保つ、pで零化された係数への多項式の標準係数射。 -/
theorem exists_completedPolyZeroCoefficientMap :
    ∃ f : completedPoly k T p →ₐ[k] MvPolynomial T l,
      ∀ x : MvPolynomial T k,
        f (principalCompletionUnitRingHom (MvPolynomial T k) (p : MvPolynomial T k) x) =
          MvPolynomial.map (algebraMap k l) x := by
  have hpP : (p : MvPolynomial T l) = 0 := by
    rw [← map_natCast (MvPolynomial.C : l →+* MvPolynomial T l), hp, map_zero]
  let β := principalCompletionMap (MvPolynomial.map (algebraMap k l))
    (p : MvPolynomial T k) (p : MvPolynomial T l) (map_natCast _ p)
  let e := crystallinePrincipalCompletionOfZero (p : MvPolynomial T l) hpP
  have hu (x : MvPolynomial T k) :
      e (β (principalCompletionUnitRingHom _ _ x)) = MvPolynomial.map (algebraMap k l) x := by
    have h := RingHom.congr_fun (principalCompletionMap_comp (MvPolynomial.map (algebraMap k l))
      (p : MvPolynomial T k) (p : MvPolynomial T l) (map_natCast _ p)) x
    change β (principalCompletionUnitRingHom _ _ x) =
      principalCompletionUnitRingHom _ _ (MvPolynomial.map (algebraMap k l) x) at h
    rw [h]
    exact crystallinePrincipalCompletionOfZero_unit _ hpP _
  let F : completedPoly k T p →ₐ[k] MvPolynomial T l :=
    { __ := e.toRingHom.comp β
      commutes' := fun a => by
        change e (β (principalCompletionUnitRingHom _ _ (MvPolynomial.C a))) = _
        rw [hu, MvPolynomial.map_C]
        rfl }
  exact ⟨F, hu⟩

omit hp

/-- pが零の環への元の完備多項式環の射は、元の多項式の単位の値で決まる。 -/
theorem completedPolyRingHom_ext_to_zero {D : Type u} [CommRing D] (hpD : (p : D) = 0)
    (g h : completedPoly k T p →+* D)
    (he : g.comp (principalCompletionUnitRingHom _ _) =
      h.comp (principalCompletionUnitRingHom _ _)) : g = h := by
  let R := MvPolynomial T k
  let z := h.comp (principalCompletionUnitRingHom R (p : R))
  letI := z.toAlgebra
  have ht : IsModuleComplete R (p : R) (ModuleCat.of R D) := by
    apply (isModuleComplete_algebraMap_iff R D (p : R) D).mp
    change IsModuleComplete D (z (p : R)) (ModuleCat.of D D)
    rw [map_natCast, hpD]
    exact isModuleComplete_of_pow_smul_zero D 0 _ 1 (by intro x; simp)
  exact (principalCompletion_existsUnique_ringHom R (p : R) D z ht).unique he rfl

include hp
/-- 元のp完備多項式環の係数拡大は、元の単位純テンソルを保って通常多項式環と同型。 -/
theorem exists_completedPolyZeroBaseChangeEquiv :
    ∃ e : (l ⊗[k] completedPoly k T p) ≃ₐ[l] MvPolynomial T l,
      ∀ (a : l) (x : MvPolynomial T k),
        e (a ⊗ₜ[k] principalCompletionUnitRingHom _ _ x) =
          a • MvPolynomial.map (algebraMap k l) x := by
  let C := completedPoly k T p
  let Z := l ⊗[k] C
  let u : MvPolynomial T k →ₐ[k] C :=
    { __ := principalCompletionUnitRingHom _ _, commutes' := fun _ => rfl }
  let m : MvPolynomial T k →ₐ[k] MvPolynomial T l :=
    { __ := MvPolynomial.map (algebraMap k l)
      commutes' := fun a => by
        change MvPolynomial.map (algebraMap k l) (MvPolynomial.C a) =
          MvPolynomial.C (algebraMap k l a)
        exact MvPolynomial.map_C _ a }
  obtain ⟨f, hf⟩ := exists_completedPolyZeroCoefficientMap k l T p hp
  have hf' (x : MvPolynomial T k) : f (u x) = MvPolynomial.map (algebraMap k l) x := hf x
  let F : Z →ₐ[l] MvPolynomial T l := AlgHom.liftEquiv k l C (MvPolynomial T l) f
  let G : MvPolynomial T l →ₐ[l] Z := MvPolynomial.aeval
    (fun j => (1 : l) ⊗ₜ[k] u (MvPolynomial.X j))
  have hGu : (G.restrictScalars k).comp m = Algebra.TensorProduct.includeRight.comp u := by
    apply MvPolynomial.algHom_ext
    intro j
    change G (MvPolynomial.map (algebraMap k l) (MvPolynomial.X j)) =
      (1 : l) ⊗ₜ[k] u (MvPolynomial.X j)
    rw [MvPolynomial.map_X]
    exact MvPolynomial.aeval_X _ _
  have hF (x : MvPolynomial T k) : F ((1 : l) ⊗ₜ[k] u x) = MvPolynomial.map (algebraMap k l) x := by
    calc
      F ((1 : l) ⊗ₜ[k] u x) = (1 : l) • f (u x) := AlgHom.liftEquiv_tmul f 1 (u x)
      _ = _ := by rw [one_smul]; exact hf' x
  have hFG : F.comp G = AlgHom.id l (MvPolynomial T l) := by
    apply MvPolynomial.algHom_ext
    intro j
    change F (G (MvPolynomial.X j)) = MvPolynomial.X j
    rw [show G (MvPolynomial.X j) = (1 : l) ⊗ₜ[k] u (MvPolynomial.X j) from
      MvPolynomial.aeval_X _ _, hF, MvPolynomial.map_X]
  have hpZ : (p : Z) = 0 := by
    rw [← map_natCast (algebraMap l Z), hp, map_zero]
  have hGF : G.comp F = AlgHom.id l Z := by
    apply Algebra.TensorProduct.ext_ring
    apply AlgHom.ext
    intro x
    let h₁ : C →+* Z := ((G.toRingHom.comp F.toRingHom).comp
      Algebra.TensorProduct.includeRight.toRingHom)
    let h₂ : C →+* Z := Algebra.TensorProduct.includeRight.toRingHom
    have hh : h₁ = h₂ := by
      apply completedPolyRingHom_ext_to_zero k T p hpZ
      apply RingHom.ext
      intro y
      change G (F ((1 : l) ⊗ₜ[k] u y)) = (1 : l) ⊗ₜ[k] u y
      rw [hF]
      exact AlgHom.congr_fun hGu y
    exact RingHom.congr_fun hh x
  refine ⟨{ __ := F, invFun := G, left_inv := ?_, right_inv := ?_ }, ?_⟩
  · intro x
    exact AlgHom.congr_fun hGF x
  · intro x
    exact AlgHom.congr_fun hFG x
  · intro a x
    change F (a ⊗ₜ[k] u x) = _
    change a • f (u x) = _
    rw [hf']

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
