module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumn
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumn
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionLinearMap

/-!
# 完備 pd 係数の偏微分の Leibniz 則

## 概要
分冪偏微分の完備化は導分の積公式を保つ。

## 方針
二つの係数線形写像が完備化単位の像で一致することを示し、二変数に延長する。

## 規約
第 0 頂点と差座標で偏微分する。

## 使われ方
pd de Rham 複体の外積と総複体の積。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) (k : Type u) [CommRing k] (r n : ℕ)

/-- 完備 pd 座標の偏微分。 -/
abbrev pdCompletedPartial (a : pdCoordinates r n) : pdTerm p k r n →ₗ[k] pdTerm p k r n :=
  principalCompletionLinearMap k p (pdRawPartial k r n a)

set_option backward.isDefEq.respectTransparency false in
/-- 完備 pd 偏微分は積について導分則を満たす。 -/
theorem pdCompletedPartial_mul (a : pdCoordinates r n) (x y : pdTerm p k r n) :
    pdCompletedPartial p k r n a (x * y) =
      pdCompletedPartial p k r n a x * y + x * pdCompletedPartial p k r n a y := by
  let B := pdRaw k r n
  let Q := pdTerm p k r n
  let J := principalCompletionRingCatUnit p (CommRingCat.of B)
  let D := pdCompletedPartial p k r n a
  let M := LinearMap.mul k Q
  let F := M.compr₂ D
  let G := M.comp D + M.compl₂ D
  have hc : IsModuleComplete k (p : k) (ModuleCat.of k Q) :=
    completedRing_isModuleComplete k p (A := B)
  have h (b c : B) : F (J b) (J c) = G (J b) (J c) := by
    change D (J b * J c) = D (J b) * J c + J b * D (J c)
    have hD (z : B) : D (J z) = J (pdRawPartial k r n a z) :=
      principalCompletionLinearMap_unit k p (A := B) (B := B) _ z
    rw [← map_mul, hD, hD, hD, ← map_mul, ← map_mul, ← map_add]
    congr 1
    let d := pdRawDerivation k r n a
    have hd := d.leibniz b c
    have e := pdRawDerivation_toLinearMap k r n a
    change d.toLinearMap (b * c) = b * d.toLinearMap c + c * d.toLinearMap b at hd
    rw [show d.toLinearMap = pdRawPartial k r n a from e] at hd
    rw [mul_comm (pdRawPartial k r n a b) c, add_comm]
    exact hd
  have h' (b : B) : F (J b) = G (J b) :=
    principalCompletionLinearMap_ext k p (A := B) hc (h b)
  have h'' (z : Q) : F.flip z = G.flip z := by
    apply principalCompletionLinearMap_ext k p (A := B) hc
    intro b
    exact DFunLike.congr_fun (h' b) z
  exact DFunLike.congr_fun (h'' y) x

end SerrePositivity.BhattScholze.Prismatic
