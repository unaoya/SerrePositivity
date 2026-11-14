module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamWedge
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamBicomplex
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.AWBilinear
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.AWBilinear
public import SerrePositivity.HomologicalAlgebra.BicomplexComponents
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRow
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamBicomplex

/-!
# pd de Rham 総複体の Alexander–Whitney 積

## 概要
横方向の Alexander–Whitney 積と、縦方向の pd 外積を組み合わせる。

## 方針
双次数ごとの積を定義し、総複体の有限直和の成分から積を作る。

## 規約
左の外次数 b と右の単体次数 c を交換する符号は (−1)^(b * c)。

## 使われ方
総複体からの二つの射影の乗法性。
-/

public noncomputable section

open CategoryTheory SerrePositivity.HomologicalAlgebra SerrePositivity.Cosimplicial
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) (k : Type u) [CommRing k] (r : ℕ)

local notation "K" => pdDeRhamDoubleComplex p k r
local notation "T" => pdDeRhamTotal p k r

/-- 双次数を固定した、符号を含む Alexander–Whitney 外積。 -/
def pdBigradedProduct (a b c d : ℕ) :
    ((K).X a).X b →ₗ[k] ((K).X c).X d →ₗ[k] ((K).X (a + c)).X (b + d) :=
  (-1 : ℤ)^(b * c) •
    (pdWedge p k r ⦋a + c⦌ b d).compl₁₂
      (((pdRow p k r b).map (frontFace a c)).hom)
      (((pdRow p k r d).map (backFace a c)).hom)

/-- 双次数を固定した積の値を余単体的な双線形対で読む。 -/
private theorem pdBigradedProduct_apply (a b c d : ℕ) (x : ((K).X a).X b) (y : ((K).X c).X d) :
    pdBigradedProduct p k r a b c d x y =
      (-1 : ℤ)^(b * c) • awBilinear (pdRow p k r b) (pdRow p k r d) (pdRow p k r (b + d))
        (fun n => pdWedge p k r n b d) (m := a) (n := c) x y := by
  unfold pdBigradedProduct awBilinear
  rfl

private def totalSummandProduct (i j : ℕ) (s : totalIndex i) (t : totalIndex j) :
    (T).X i →ₗ[k] (T).X j →ₗ[k] (T).X (i + j) :=
  let u : totalIndex (i + j) := ⟨(s.1.1 + t.1.1, s.1.2 + t.1.2), by
    have _hs := s.2
    have _ht := t.2
    omega⟩
  ((pdBigradedProduct p k r s.1.1 s.1.2 t.1.1 t.1.2).compr₂
    (insertAt K (i + j) u).hom).compl₁₂ (componentAt K i s).hom (componentAt K j t).hom

/-- 総複体上の外積は、双次数ごとの Alexander–Whitney 外積の和。 -/
def pdTotalProduct (i j : ℕ) :
    (T).X i →ₗ[k] (T).X j →ₗ[k] (T).X (i + j) :=
  ∑ s : totalIndex i, ∑ t : totalIndex j, totalSummandProduct p k r i j s t

private theorem totalSummandProduct_apply (i j : ℕ) (s : totalIndex i) (t : totalIndex j)
    (x : (T).X i) (y : (T).X j) :
    totalSummandProduct p k r i j s t x y =
      insertAt K (i + j) ⟨(s.1.1 + t.1.1, s.1.2 + t.1.2), by
        have _hs := s.2
        have _ht := t.2
        omega⟩
        (pdBigradedProduct p k r s.1.1 s.1.2 t.1.1 t.1.2
          (componentAt K i s x) (componentAt K j t y)) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- 二つの挿入の積は双次数を足した成分への挿入。 -/
theorem pdTotalProduct_insert (i j : ℕ) (s : totalIndex i) (t : totalIndex j)
    (x : ((K).X s.1.1).X s.1.2) (y : ((K).X t.1.1).X t.1.2) :
    pdTotalProduct p k r i j (insertAt K i s x) (insertAt K j t y) =
      insertAt K (i + j) ⟨(s.1.1 + t.1.1, s.1.2 + t.1.2), by
        have _hs := s.2
        have _ht := t.2
        omega⟩
        (pdBigradedProduct p k r s.1.1 s.1.2 t.1.1 t.1.2 x y) := by
  classical
  simp only [pdTotalProduct, LinearMap.sum_apply, totalSummandProduct_apply]
  rw [Finset.sum_eq_single s]
  · have hx := ConcreteCategory.congr_hom (insertAt_componentAt_eq K s) x
    change componentAt K i s (insertAt K i s x) = x at hx
    simp only [hx]
    rw [Finset.sum_eq_single t]
    · have hy := ConcreteCategory.congr_hom (insertAt_componentAt_eq K t) y
      change componentAt K j t (insertAt K j t y) = y at hy
      rw [hy]
    · intro t' _ ht'
      have h := ConcreteCategory.congr_hom (insertAt_componentAt_ne K t t' ht'.symm) y
      change componentAt K j t' (insertAt K j t y) = 0 at h
      rw [h, map_zero, map_zero]
    · simp
  · intro s' _ hs'
    apply Finset.sum_eq_zero
    intro t' _
    have h := ConcreteCategory.congr_hom (insertAt_componentAt_ne K s s' hs'.symm) x
    change componentAt K i s' (insertAt K i s x) = 0 at h
    rw [h, map_zero, LinearMap.zero_apply, map_zero]
  · simp

end SerrePositivity.BhattScholze.Prismatic
