module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamTotalProduct
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamTotalProduct
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamBicomplex
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.AWBilinear

/-!
# pd の双次数での積の微分

## 概要
Alexander–Whitney 外積の横微分・縦微分を符号付きの積に分解する。

## 方針
余面方向の Leibniz 則と列の外積の Leibniz 則を、それぞれ総複体の符号に合わせる。

## 規約
双次数 (a,b) の左因子の総次数は a+b。

## 使われ方
総複体の積の Leibniz 則。
-/

public noncomputable section

open CategoryTheory AlgebraicTopology SerrePositivity.Cosimplicial
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) (k : Type u) [CommRing k] (r : ℕ)
local notation "K" => pdDeRhamDoubleComplex p k r

private theorem horizontalCast_zsmul (j : ℕ) {a b : ℕ} (h : a = b)
    (z : ℤ) (x : ((K).X a).X j) :
    cast (congrArg (fun n => (((K).X n).X j : Type u)) h) (z • x) =
      z • cast (congrArg (fun n => (((K).X n).X j : Type u)) h) x := by
  subst b
  rfl

private theorem horizontal_d_eq (a b : ℕ) :
    ((K).d a (a+1)).f b = moduleCofaceDifferential (pdRow p k r b) a := by
  change (AlternatingCofaceMapComplex.obj (pdRow p k r b)).d a (a+1) = _
  dsimp only [AlternatingCofaceMapComplex.obj, CochainComplex.of]
  rw [CochainComplex.of_d]
  rfl

private theorem horizontal_sign (a b c : ℕ) :
    (-1 : ℤ)^(b*c) * (-1 : ℤ)^a = (-1 : ℤ)^(a+b) * (-1 : ℤ)^(b*(c+1)) := by
  rw [← pow_add, ← pow_add]
  have h : a+b+b*(c+1) = (b*c+a) + 2*b := by ring
  rw [h, pow_add (-1 : ℤ) (b*c+a), pow_mul (-1 : ℤ) 2 b]
  norm_num

set_option maxHeartbeats 1600000 in
-- 双複体の項と余単体模型の項を照合する。
set_option backward.isDefEq.respectTransparency false in
/-- 積の横微分は余面の Leibniz 則を満たす。 -/
theorem pdBigradedProduct_horizontal (a b c d : ℕ) (x : ((K).X a).X b) (y : ((K).X c).X d) :
    ((K).d (a+c) (a+c+1)).f (b+d) (pdBigradedProduct p k r a b c d x y) =
      cast (congrArg (fun n => (((K).X n).X (b+d) : Type u)) (by omega : a+1+c = a+c+1))
        (pdBigradedProduct p k r (a+1) b c d (((K).d a (a+1)).f b x) y) +
      (-1 : ℤ)^(a+b) • pdBigradedProduct p k r a b (c+1) d x (((K).d c (c+1)).f d y) := by
  have h := moduleCofaceDifferential_awBilinear
    (pdRow p k r b) (pdRow p k r d) (pdRow p k r (b+d)) (fun n => pdWedge p k r n b d)
    (fun θ f g => pdWedge_natural p k r θ b d f g) (m := a) (n := c) x y
  rw [pdBigradedProduct_apply, pdBigradedProduct_apply, pdBigradedProduct_apply,
    map_zsmul, horizontal_d_eq, horizontal_d_eq, horizontal_d_eq]
  erw [h]
  erw [smul_add, smul_smul, horizontalCast_zsmul, smul_smul, horizontal_sign] <;>
    first | rfl | omega

private theorem verticalCast_zsmul (a : ℕ) {b d : ℕ} (h : b = d)
    (z : ℤ) (x : ((K).X a).X b) :
    cast (congrArg (fun n => (((K).X a).X n : Type u)) h) (z • x) =
      z • cast (congrArg (fun n => (((K).X a).X n : Type u)) h) x := by
  subst d
  rfl

private theorem vertical_d_eq (a j : ℕ) :
    ((K).X a).d j (j+1) = pdVerticalD p k r ⦋a⦌ j :=
  column_d_eq p k r a j

private theorem verticalMap_apply {m n : SimplexCategory} (θ : m ⟶ n) (j : ℕ)
    (x : (pdRow p k r j).obj m) :
    pdVerticalD p k r n j ((pdRow p k r j).map θ x) =
      (pdRow p k r (j+1)).map θ (pdVerticalD p k r m j x) :=
  ConcreteCategory.congr_hom ((pdDeRhamDifferential p k r j).naturality θ) x

private theorem vertical_left_sign (a b c : ℕ) :
    (-1 : ℤ)^(a+c) * (-1 : ℤ)^(b*c) = (-1 : ℤ)^a * (-1 : ℤ)^((b+1)*c) := by
  rw [← pow_add, ← pow_add]
  congr 1
  ring

private theorem vertical_right_sign (a b c : ℕ) :
    ((-1 : ℤ)^(a+c) * (-1 : ℤ)^(b*c)) * (-1 : ℤ)^b =
      (-1 : ℤ)^(a+b) * ((-1 : ℤ)^c * (-1 : ℤ)^(b*c)) := by
  rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
  congr 1
  ring

set_option maxHeartbeats 1600000 in
-- 双複体の項と余単体模型の項を照合する。
set_option backward.isDefEq.respectTransparency false in
/-- 積の符号付き縦微分は二つの積に分解する。 -/
theorem pdBigradedProduct_vertical (a b c d : ℕ) (x : ((K).X a).X b) (y : ((K).X c).X d) :
    (-1 : ℤ)^(a+c) •
      (((K).X (a+c)).d (b+d) (b+d+1) (pdBigradedProduct p k r a b c d x y)) =
      cast (congrArg (fun n => (((K).X (a+c)).X n : Type u)) (by omega : b+1+d = b+d+1))
        ((-1 : ℤ)^a • pdBigradedProduct p k r a (b+1) c d (((K).X a).d b (b+1) x) y) +
      (-1 : ℤ)^(a+b) • ((-1 : ℤ)^c •
        pdBigradedProduct p k r a b c (d+1) x (((K).X c).d d (d+1) y)) := by
  rw [pdBigradedProduct_apply, pdBigradedProduct_apply, pdBigradedProduct_apply,
    vertical_d_eq, vertical_d_eq, vertical_d_eq]
  unfold awBilinear
  erw [map_zsmul, smul_smul, pdVerticalD_wedge, smul_add,
    verticalMap_apply, verticalMap_apply, smul_smul, verticalCast_zsmul,
    smul_smul, vertical_left_sign] <;> try omega
  have hs : (-1 : ℤ)^a * (-1 : ℤ)^((b+1)*c) * (-1 : ℤ)^b =
      (-1 : ℤ)^(a+b) * (-1 : ℤ)^c * (-1 : ℤ)^(b*c) := by
    rw [← vertical_left_sign, vertical_right_sign, mul_assoc]
  erw [hs, verticalCast_zsmul, smul_smul, smul_smul] <;> first | rfl | omega

end SerrePositivity.BhattScholze.Prismatic
