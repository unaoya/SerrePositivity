module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedDerivation
public import SerrePositivity.CommutativeAlgebra.DeRham.PolynomialLeibniz
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumn
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRow
import all SerrePositivity.CommutativeAlgebra.DeRham.PolynomialLeibniz

/-!
# pd de Rham 列の外積

## 概要
同じ単体次数の pd 微分形式に外積を入れ、分冪微分の Leibniz 則を示す。

## 方針
純テンソル上では完備 pd 偏微分の積公式と、外冪の反交換則に帰着する。

## 規約
外積の係数は完備 pd 環で掛ける。

## 使われ方
pd de Rham 総複体の積。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DeRham
open scoped TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) (k : Type u) [CommRing k] (r : ℕ) (n : SimplexCategory)

local notation "A" => pdTerm p k r n.len
local notation "M" => CopyModule k r n
local notation "E[" j "]" => (⋀[k]^j M)
local notation "F[" j "]" => (A ⊗[k] E[j])

private def wedgeTensor (i j : ℕ) : F[i] →ₗ[k] F[j] →ₗ[k] F[i + j] :=
  TensorProduct.map₂ (LinearMap.mul k A) (exteriorWedge k M i j)

/-- pd 列の外積は完備係数の積と頂点の外冪の積のテンソル。 -/
def pdWedge (i j : ℕ) : ((pdRow p k r (i)).obj n) →ₗ[k] ((pdRow p k r (j)).obj n) →ₗ[k] ((pdRow p k r (i + j)).obj n) :=
  wedgeTensor p k r n i j

private def pdWedgeD (i : ℕ) : F[i] →ₗ[k] F[i + 1] := (pdVerticalD p k r n i).hom

private theorem pdWedgeD_eq (i : ℕ) :
    pdWedgeD p k r n i =
      ∑ t : pdCoordinates r n.len, TensorProduct.map (pdCompletedPartial p k r n.len t)
        (wedgeOne k M i (pdCoordinateOne k r n t)) :=
  rfl

private theorem castW_add {i j : ℕ} (h : i = j) (a b : F[i]) :
    cast (congrArg (fun t => (F[t] : Type u)) h) (a + b) =
      cast (congrArg (fun t => (F[t] : Type u)) h) a +
      cast (congrArg (fun t => (F[t] : Type u)) h) b := by
  subst j
  rfl

private theorem castW_sum {ι : Type*} {i j : ℕ} (h : i = j) (s : Finset ι) (f : ι → F[i]) :
    cast (congrArg (fun t => (F[t] : Type u)) h) (∑ a ∈ s, f a) =
      ∑ a ∈ s, cast (congrArg (fun t => (F[t] : Type u)) h) (f a) := by
  subst j
  rfl

private theorem castW_tmul {i j : ℕ} (h : i = j) (f : A) (b : E[i]) :
    cast (congrArg (fun t => (F[t] : Type u)) h) (f ⊗ₜ[k] b) =
      f ⊗ₜ[k] cast (congrArg (fun t => ↥(E[t])) h) b := by
  subst j
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- テンソル表示で係数と外冪の Leibniz 則を照合する。
/-- 分冪微分は pd 列の外積について符号付き Leibniz 則を満たす。 -/
theorem pdVerticalD_wedge {i j : ℕ} (x : ((pdRow p k r (i)).obj n)) (y : ((pdRow p k r (j)).obj n)) :
    pdVerticalD p k r n (i + j) (pdWedge p k r n i j x y) =
      cast (congrArg (fun t => (((pdRow p k r (t)).obj n) : Type u)) (by omega : (i + 1) + j = (i + j) + 1))
        (pdWedge p k r n (i + 1) j (pdVerticalD p k r n i x) y) +
      (-1 : ℤ)^i • pdWedge p k r n i (j + 1) x (pdVerticalD p k r n j y) := by
  let e : (i + 1) + j = (i + j) + 1 := by omega
  change pdWedgeD p k r n (i + j) (wedgeTensor p k r n i j x y) =
    cast (congrArg (fun t => (F[t] : Type u)) e)
      (wedgeTensor p k r n (i + 1) j (pdWedgeD p k r n i x) y) +
    (-1 : ℤ)^i • wedgeTensor p k r n i (j + 1) x (pdWedgeD p k r n j y)
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' =>
    simp only [map_add, LinearMap.add_apply, smul_add] at hx hx' ⊢
    rw [castW_add p k r n e, hx, hx']
    ac_rfl
  | tmul f b =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' =>
      simp only [map_add, smul_add] at hy hy' ⊢
      rw [castW_add p k r n e, hy, hy']
      ac_rfl
    | tmul g c =>
      change A at f g
      change E[i] at b
      change E[j] at c
      simp only [pdWedgeD_eq, LinearMap.sum_apply, TensorProduct.map_tmul]
      simp only [wedgeTensor, map_sum, LinearMap.sum_apply, TensorProduct.map₂_apply_tmul,
        TensorProduct.map_tmul]
      rw [castW_sum p k r n e, Finset.smul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t _
      let v := pdCoordinateOne k r n t
      let w := wedgeOne k M (i + j) v (exteriorWedge k M i j b c)
      let l := exteriorWedge k M (i + 1) j (wedgeOne k M i v b) c
      let r' := exteriorWedge k M i (j + 1) b (wedgeOne k M j v c)
      let D := pdCompletedPartial p k r n.len t
      change D (f * g) ⊗ₜ[k] w =
        cast (congrArg (fun t => (F[t] : Type u)) e) ((D f * g) ⊗ₜ[k] l) +
          (-1 : ℤ)^i • ((f * D g) ⊗ₜ[k] r')
      have h := pdCompletedPartial_mul p k r n.len t f g
      change D (f * g) = D f * g + f * D g at h
      rw [h, TensorProduct.add_tmul, castW_tmul p k r n e, ← TensorProduct.tmul_smul]
      congr 1
      · exact congrArg (fun x : E[i + j + 1] => (D f * g) ⊗ₜ[k] x)
          (wedgeOne_mul_left k M v b c)
      · exact congrArg (fun x : E[i + j + 1] => (f * D g) ⊗ₜ[k] x)
          (wedgeOne_mul_right k M (pdCoordinateVector k r n t) b c)

private theorem exteriorWedge_map {N : Type u} [AddCommGroup N] [Module k N]
    (f : M →ₗ[k] N) {i j : ℕ} (a : E[i]) (b : E[j]) :
    exteriorPower.map (i + j) f (exteriorWedge k M i j a b) =
      exteriorWedge k N i j (exteriorPower.map i f a) (exteriorPower.map j f b) := by
  apply Subtype.ext
  have h (j : ℕ) (z : E[j]) :
      (exteriorPower.map j f z).1 = ExteriorAlgebra.map f z.1 :=
    DFunLike.congr_fun (exteriorPower.subtype_comp_map_eq (n := j) f) z
  rw [h]
  change ExteriorAlgebra.map f (a.1 * b.1) =
    (exteriorPower.map i f a).1 * (exteriorPower.map j f b).1
  rw [map_mul, h, h]

private theorem pdTermMap_mul {m n : SimplexCategory} (θ : m ⟶ n)
    (f g : pdTerm p k r m.len) :
    pdTermMap p k r θ (f * g) = pdTermMap p k r θ f * pdTermMap p k r θ g := by
  exact map_mul (SerrePositivity.DerivedCompletion.ringCatMap p (rawTermMap k r θ)).hom f g

set_option backward.isDefEq.respectTransparency false in
-- 余単体構造射を係数と外冪に分けて調べる。
/-- pd 列の外積は余単体の構造射で保存される。 -/
theorem pdWedge_natural {m n : SimplexCategory} (θ : m ⟶ n) (i j : ℕ)
    (x : (pdRow p k r i).obj m) (y : (pdRow p k r j).obj m) :
    (pdRow p k r (i + j)).map θ (pdWedge p k r m i j x y) =
      pdWedge p k r n i j ((pdRow p k r i).map θ x) ((pdRow p k r j).map θ y) := by
  let F (l : ℕ) := TensorProduct.map (pdTermMap p k r θ) (exteriorPower.map l (copyModuleMap k r θ))
  change F (i + j) (wedgeTensor p k r m i j x y) =
    wedgeTensor p k r n i j (F i x) (F j y)
  induction x using TensorProduct.inductionOn with
  | add a a' ha ha' =>
    simp only [map_add, LinearMap.add_apply] at ha ha' ⊢
    rw [ha, ha']
  | tmul f a =>
    induction y using TensorProduct.inductionOn with
    | add b b' hb hb' => simp only [map_add, hb, hb']
    | tmul g b =>
      change pdTerm p k r m.len at f g
      change ⋀[k]^i (CopyModule k r m) at a
      change ⋀[k]^j (CopyModule k r m) at b
      simp only [wedgeTensor, F, TensorProduct.map₂_apply_tmul, TensorProduct.map_tmul,
        LinearMap.mul_apply', pdTermMap_mul, exteriorWedge_map]

end SerrePositivity.BhattScholze.Prismatic
