module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamAxisProduct
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamTotalLeibniz
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamTotalProduct
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamBicomplex
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamAxisProduct
import all SerrePositivity.HomologicalAlgebra.BicomplexProjection
import all SerrePositivity.HomologicalAlgebra.BicomplexComponents
import all SerrePositivity.HomologicalAlgebra.BicomplexProductLeibniz

/-!
# pd de Rham 総複体の二つの射影と積

## 概要
第 0 行と第 0 列への射影はそれぞれの余鎖積を保つ。

## 方針
挿入した成分で確認する。軸から外れた成分を一つでも含む積は射影で消える。

## 規約
添字の二成分の和を総次数とする。

## 使われ方
pd de Rham 比較のコホモロジー積。
-/

public noncomputable section

open CategoryTheory SerrePositivity.HomologicalAlgebra SerrePositivity.Cosimplicial AlgebraicTopology
open scoped Simplicial

universe u

namespace SerrePositivity.HomologicalAlgebra

variable {k : Type u} [CommRing k]
local notation "up" => ComplexShape.up ℕ
variable (K : HomologicalComplex₂ (ModuleCat.{u} k) up up) [K.HasTotal up]

private theorem rowProjection_off {n a b : ℕ} (h : a+b=n) (hb : b ≠ 0) (x : (K.X a).X b) :
    (totalToRowZero K).f n (insertAt K n ⟨(a,b),h⟩ x) = 0 := by
  have hh : insertAt K n ⟨(a,b),h⟩ ≫ (totalToRowZero K).f n = 0 := by
    simp [insertAt, totalToRowZero, rowZeroApp, hb]
  simpa only [ConcreteCategory.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using
    ConcreteCategory.congr_hom hh x

private theorem rowProjection_on (n : ℕ) (x : (K.X n).X 0) :
    (totalToRowZero K).f n (insertAt K n ⟨(n,0),Nat.add_zero _⟩ x) = x := by
  have hh : insertAt K n ⟨(n,0),Nat.add_zero _⟩ ≫ (totalToRowZero K).f n = 𝟙 _ := by
    simp [insertAt, totalToRowZero, rowZeroApp, bicomplexRow]
  simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
    ConcreteCategory.congr_hom hh x

private theorem columnProjection_off {n a b : ℕ} (h : a+b=n) (ha : a ≠ 0) (x : (K.X a).X b) :
    (totalToColumnZero K).f n (insertAt K n ⟨(a,b),h⟩ x) = 0 := by
  have hh : insertAt K n ⟨(a,b),h⟩ ≫ (totalToColumnZero K).f n = 0 := by
    simp [insertAt, totalToColumnZero, columnZeroApp, ha]
  simpa only [ConcreteCategory.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using
    ConcreteCategory.congr_hom hh x

private theorem columnProjection_on (n : ℕ) (x : (K.X 0).X n) :
    (totalToColumnZero K).f n (insertAt K n ⟨(0,n),Nat.zero_add _⟩ x) = x := by
  have hh : insertAt K n ⟨(0,n),Nat.zero_add _⟩ ≫ (totalToColumnZero K).f n = 𝟙 _ := by
    simp [insertAt, totalToColumnZero, columnZeroApp]
  simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
    ConcreteCategory.congr_hom hh x

end SerrePositivity.HomologicalAlgebra

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) (k : Type u) [CommRing k] (r : ℕ)
local notation "K" => pdDeRhamDoubleComplex p k r
local notation "T" => pdDeRhamTotal p k r

private theorem row_zero_bigraded (a c : ℕ) (x : ((K).X a).X 0) (y : ((K).X c).X 0) :
    pdBigradedProduct p k r a 0 c 0 x y = (pdRowZeroCochainProduct p k r).mul a c x y := by
  rw [pdBigradedProduct_apply]
  simp only [Nat.zero_mul, pow_zero, one_zsmul]
  rfl

private theorem column_zero_bigraded (b d : ℕ) (x : ((K).X 0).X b) (y : ((K).X 0).X d) :
    cast (congrArg (fun n => (((K).X n).X (b+d) : Type u)) (Nat.zero_add 0))
      (pdBigradedProduct p k r 0 b 0 d x y) = (pdColumnCochainProduct p k r 0).mul b d x y := by
  rw [cast_eq, pdBigradedProduct_apply]
  simp only [Nat.mul_zero, pow_zero, one_zsmul, awBilinear]
  have hf : frontFace 0 0 = 𝟙 _ := by
    apply SimplexCategory.Hom.ext_zero_left
    change (_ : Fin 1) = _
    exact Subsingleton.elim _ _
  have hb : backFace 0 0 = 𝟙 _ := by
    apply SimplexCategory.Hom.ext_zero_left
    change (_ : Fin 1) = _
    exact Subsingleton.elim _ _
  erw [hf, hb, (pdRow p k r b).map_id, (pdRow p k r d).map_id,
    ConcreteCategory.id_apply, ConcreteCategory.id_apply]
  rfl

private theorem rowProjection_product_insert (i j : ℕ) (s : totalIndex i) (t : totalIndex j)
    (x : ((K).X s.1.1).X s.1.2) (y : ((K).X t.1.1).X t.1.2) :
    let F := totalToRowZero K
    F.f (i+j) (pdTotalProduct p k r i j (insertAt K i s x) (insertAt K j t y)) =
      (pdRowZeroCochainProduct p k r).mul i j (F.f i (insertAt K i s x))
        (F.f j (insertAt K j t y)) := by
  obtain ⟨⟨a,b⟩, hab⟩ := s
  obtain ⟨⟨c,d⟩, hcd⟩ := t
  change a+b=i at hab
  change c+d=j at hcd
  dsimp only
  rw [pdTotalProduct_insert]
  dsimp only
  by_cases hb : b = 0
  · by_cases hd : d = 0
    · subst b d
      simp only [Nat.add_zero] at hab hcd
      subst i j
      rw [rowProjection_on, rowProjection_on, rowProjection_on]
      exact row_zero_bigraded p k r a c x y
    · erw [rowProjection_off K _ (show b+d ≠ 0 by omega),
        rowProjection_off K hcd hd, map_zero]
      rfl
  · erw [rowProjection_off K _ (show b+d ≠ 0 by omega),
      rowProjection_off K hab hb, map_zero, LinearMap.zero_apply]
    rfl

private theorem columnProjection_product_insert (i j : ℕ) (s : totalIndex i) (t : totalIndex j)
    (x : ((K).X s.1.1).X s.1.2) (y : ((K).X t.1.1).X t.1.2) :
    let F := totalToColumnZero K
    F.f (i+j) (pdTotalProduct p k r i j (insertAt K i s x) (insertAt K j t y)) =
      (pdColumnCochainProduct p k r 0).mul i j (F.f i (insertAt K i s x))
        (F.f j (insertAt K j t y)) := by
  obtain ⟨⟨a,b⟩, hab⟩ := s
  obtain ⟨⟨c,d⟩, hcd⟩ := t
  change a+b=i at hab
  change c+d=j at hcd
  dsimp only
  rw [pdTotalProduct_insert]
  dsimp only
  by_cases ha : a = 0
  · by_cases hc : c = 0
    · subst a c
      have hi : b = i := (Nat.zero_add b).symm.trans hab
      have hj : d = j := (Nat.zero_add d).symm.trans hcd
      cases hi
      cases hj
      rw [columnProjection_on, columnProjection_on, columnProjection_on]
      exact column_zero_bigraded p k r _ _ x y
    · erw [columnProjection_off K _ (show a+c ≠ 0 by omega),
        columnProjection_off K hcd hc, map_zero]
      rfl
  · erw [columnProjection_off K _ (show a+c ≠ 0 by omega),
      columnProjection_off K hab ha, map_zero, LinearMap.zero_apply]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- 第 0 行への射影は積を保つ。 -/
theorem pdRowZeroProjection_mul (i j : ℕ) (x : (T).X i) (y : (T).X j) :
    (pdDeRhamRowZeroProjection p k r).f (i+j) (pdTotalProduct p k r i j x y) =
      (pdRowZeroCochainProduct p k r).mul i j ((pdDeRhamRowZeroProjection p k r).f i x)
        ((pdDeRhamRowZeroProjection p k r).f j y) := by
  let f (a : totalIndex i) := insertAt K i a (componentAt K i a x)
  let g (b : totalIndex j) := insertAt K j b (componentAt K j b y)
  have hx : ∑ a, f a = x := total_decomposition_apply K x
  have hy : ∑ b, g b = y := total_decomposition_apply K y
  rw [← hx, ← hy]
  simp only [map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro s _
  exact rowProjection_product_insert p k r i j s t _ _

set_option backward.isDefEq.respectTransparency false in
/-- 第 0 列への射影は積を保つ。 -/
theorem pdColumnZeroProjection_mul (i j : ℕ) (x : (T).X i) (y : (T).X j) :
    (pdDeRhamColumnZeroProjection p k r).f (i+j) (pdTotalProduct p k r i j x y) =
      (pdColumnCochainProduct p k r 0).mul i j ((pdDeRhamColumnZeroProjection p k r).f i x)
        ((pdDeRhamColumnZeroProjection p k r).f j y) := by
  let f (a : totalIndex i) := insertAt K i a (componentAt K i a x)
  let g (b : totalIndex j) := insertAt K j b (componentAt K j b y)
  have hx : ∑ a, f a = x := total_decomposition_apply K x
  have hy : ∑ b, g b = y := total_decomposition_apply K y
  rw [← hx, ← hy]
  simp only [map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro s _
  exact columnProjection_product_insert p k r i j s t _ _

end SerrePositivity.BhattScholze.Prismatic
