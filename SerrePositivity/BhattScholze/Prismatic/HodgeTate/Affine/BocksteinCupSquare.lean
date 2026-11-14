module

public import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.BocksteinClass
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.BocksteinClass
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.CupCohomology

/-!
# 素数 2 での Bockstein 像の cup 平方

## 概要
余単体的 δ 環で、正則元による Bockstein の零次からの像は cup 平方が零になる。

## 方針
整係数の一次余輪体に δ を施し、二つの隣接辺の積がその余境界になることを示す。

## 規約
最初の余面の符号は正とする。

## 使われ方
Hodge–Tate 写像を外積へ延長する際の平方零条件。
-/

public noncomputable section

open CategoryTheory SerrePositivity.Cosimplicial
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze

variable [Fact (Nat.Prime 2)]

private theorem delta_add_two {A : Type u} [CommRing A] (D : DeltaStructure 2 A) (x y : A) :
    D.delta (x + y) = D.delta x + D.delta y - x * y := by
  have h : wittAdditionCarry 2 = -(MvPolynomial.X 0 * MvPolynomial.X 1) := by
    apply mul_left_cancel₀ (show (2 : MvPolynomial (Fin 2) ℤ) ≠ 0 by norm_num)
    rw [show (2 : MvPolynomial (Fin 2) ℤ) = ((2 : ℕ) : MvPolynomial (Fin 2) ℤ) by rfl,
      p_mul_wittAdditionCarry]
    ring
  rw [D.delta_add_polynomial, h]
  simp [sub_eq_add_neg]

variable (X : CosimplicialObject CommRingCat.{u})
  (D : ∀ n, DeltaStructure 2 (X.obj n))
  (hD : ∀ {m n} (θ : m ⟶ n), (D m).IsDeltaHom (D n) (X.map θ).hom)

omit [Fact (Nat.Prime 2)] in
private theorem d_one (x : X.obj ⦋1⦌) :
    cochainDifferential X 1 x =
      X.map (SimplexCategory.δ (0 : Fin 3)) x -
        X.map (SimplexCategory.δ (1 : Fin 3)) x + X.map (SimplexCategory.δ (2 : Fin 3)) x := by
  rw [cochainDifferential_apply, Fin.sum_univ_three]
  simp [sub_eq_add_neg]

omit [Fact (Nat.Prime 2)] in
private theorem cup_11 (x : X.obj ⦋1⦌) :
    cup X x x = X.map (SimplexCategory.δ (2 : Fin 3)) x *
      X.map (SimplexCategory.δ (0 : Fin 3)) x := by
  have hf : frontFace 1 1 = SimplexCategory.δ (2 : Fin 3) := by decide
  have hb : backFace 1 1 = SimplexCategory.δ (0 : Fin 3) := by decide
  rw [cup, hf, hb]

include hD in
/-- δ を一次余輪体に施すと cup 平方を表す余境界を得る。 -/
theorem delta_cochainDifferential_eq_cup_sq (x : X.obj ⦋1⦌)
    (hx : cochainDifferential X 1 x = 0) :
    cochainDifferential X 1 ((D ⦋1⦌).delta x) = cup X x x := by
  let a := X.map (SimplexCategory.δ (0 : Fin 3)) x
  let b := X.map (SimplexCategory.δ (1 : Fin 3)) x
  let c := X.map (SimplexCategory.δ (2 : Fin 3)) x
  have hh : a - b + c = 0 := (d_one X x).symm.trans hx
  have hb : b = a + c := by
    linear_combination -hh
  rw [d_one, cup_11]
  have h₀ := (hD (SimplexCategory.δ (0 : Fin 3))) x
  have h₁ := (hD (SimplexCategory.δ (1 : Fin 3))) x
  have h₂ := (hD (SimplexCategory.δ (2 : Fin 3))) x
  change X.map (SimplexCategory.δ (0 : Fin 3)) ((D ⦋1⦌).delta x) = (D ⦋2⦌).delta a at h₀
  change X.map (SimplexCategory.δ (1 : Fin 3)) ((D ⦋1⦌).delta x) = (D ⦋2⦌).delta b at h₁
  change X.map (SimplexCategory.δ (2 : Fin 3)) ((D ⦋1⦌).delta x) = (D ⦋2⦌).delta c at h₂
  rw [h₀, h₁, h₂, hb, delta_add_two]
  change _ = c * a
  ring

variable (d : ∀ n, X.obj n)
  (hd : ∀ {m n : SimplexCategory} (θ : m ⟶ n), X.map θ (d m) = d n)
  (hr : ∀ n, Function.Injective (fun x : X.obj n => d n * x))
  (k : Type u) [CommRing k]
  (ι : (Functor.const SimplexCategory).obj (CommRingCat.of k) ⟶ X)

local notation "Q" => quotPow X d hd 1
local notation "q" => quotProjection X d hd 1

set_option maxHeartbeats 800000 in
include hD in
/-- 素数 2 の余単体的 δ 環では Bockstein の零次からの像の cup 平方は零。 -/
theorem cupBockstein_cup_sq_two (a : cohomology Q 0) :
    let b := cupBockstein X d hd hr k ι 0 a
    cohomologyCup Q b b = 0 := by
  dsimp only
  obtain ⟨a, rfl⟩ := cohomologyClass_surjective Q 0 a
  obtain ⟨x, y, hx, hxy⟩ := exists_regularCocycleLift X d hd 0 a
  have hy := cochainDifferential_eq_zero_of_eq_mul X d hd hr 0 x y hxy
  let z := projectCycle X d hd 1 y hy
  rw [cupBockstein_class X d hd hr k ι 0 a z x y hx rfl hxy, cohomologyCup_class]
  change (cohomologyQuotientIso Q 2).inv (QuotientAddGroup.mk (cocycleCup Q z z)) = 0
  suffices h : cocycleCup Q z z ∈ boundaries Q 2 by
    rw [(QuotientAddGroup.eq_zero_iff _).mpr h, map_zero]
  apply (isBoundary_iff Q (i := 1) (j := 2) rfl _).mpr
  refine ⟨(q).app ⦋1⦌ ((D ⦋1⦌).delta y), ?_⟩
  change cochainDifferential Q 1 ((q).app ⦋1⦌ ((D ⦋1⦌).delta y)) = cup Q ((q).app ⦋1⦌ y) ((q).app ⦋1⦌ y)
  rw [← cochainDifferential_natural X Q q 1, delta_cochainDifferential_eq_cup_sq X D hD y hy]
  exact (cup_natural X q y y).symm

end SerrePositivity.BhattScholze
