module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFiniteness
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
概要：有限個の複体への分裂写像からコホモロジーの有限性を移す。
方針：各成分のコホモロジーへの写像をまとめ、分裂の和の恒等式で単射性を示す。
規約：有限個の対象。係数環は Noether。
使われ方：多項式環の捻りの有限性を、その有限直和に移す。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

open CategoryTheory
open scoped BigOperators

variable {R κ : Type*} [CommRing R] [IsNoetherianRing R] [Fintype κ]

/-- 有限個の複体への射影と包含が恒等を分解すれば、有限性は元の複体にも戻る。 -/
theorem projectiveCechHomology_finite_of_finite_splitting
    (K : CochainComplex (ModuleCat R) ℕ) (L : κ → CochainComplex (ModuleCat R) ℕ)
    (p : ∀ j, K ⟶ L j) (i : ∀ j, L j ⟶ K) (h : ∑ j, p j ≫ i j = 𝟙 K)
    (q : ℕ) (hfinite : ∀ j, Module.Finite R ((L j).homology q)) :
    Module.Finite R (K.homology q) := by
  classical
  let H := HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) q
  let f : K.homology q →ₗ[R] (j : κ) → (L j).homology q :=
    LinearMap.pi fun j ↦ (H.map (p j)).hom
  letI (j : κ) : Module.Finite R ((L j).homology q) := hfinite j
  have hs : ∑ j, H.map (p j) ≫ H.map (i j) = 𝟙 (K.homology q) := by
    simp_rw [← H.map_comp]
    rw [← Functor.map_sum, h, H.map_id]
    rfl
  have hsum (x : K.homology q) :
      ∑ j, (H.map (i j)).hom ((H.map (p j)).hom x) = x := by
    have he := congrArg ModuleCat.Hom.hom hs
    simp only [ModuleCat.hom_sum, ModuleCat.hom_comp, ModuleCat.hom_id] at he
    have hx := LinearMap.congr_fun he x
    simp only [LinearMap.sum_apply, LinearMap.comp_apply] at hx
    exact hx
  apply Module.Finite.of_injective f
  intro x y hxy
  calc
    x = ∑ j, (H.map (i j)).hom ((H.map (p j)).hom x) := (hsum x).symm
    _ = ∑ j, (H.map (i j)).hom ((H.map (p j)).hom y) := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (H.map (i j)).hom (congrFun hxy j)
    _ = y := hsum y

end SerrePositivity.AlgebraicGeometry
