module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDColumnContraction
public import SerrePositivity.CommutativeAlgebra.DeRham.ExteriorCoordinateProjection
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDRawDeRhamColumn
import all SerrePositivity.CommutativeAlgebra.DeRham.ExteriorTensorContraction

/-!
# pd 列の一座標評価

## 概要
差座標とその一次形式を零に送る評価は、鎖の上で恒等写像とホモトピック。

## 方針
分冪積分の収縮公式を外冪の座標射影と照合する。

## 規約
標数 p で完備列を未完備模型に置き換えて使う。

## 使われ方
すべての差座標を消す pd Poincaré 補題。
-/

public noncomputable section

open CategoryTheory HomologicalComplex Homotopy SerrePositivity.DeRham
open scoped TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) (k : Type u) [CommRing k] (r : ℕ) (hp : (p : k) = 0)
  (n : SimplexCategory) (s : Fin r × Fin n.len)

local notation "K" => pdRawDeRhamColumn p k r hp n

private def pdRawCoordinateHomotopyFamily (i j : ℕ) (h : (ComplexShape.up ℕ).Rel j i) : (K).X i ⟶ (K).X j := by
  have hi : j + 1 = i := h
  subst i
  exact ModuleCat.ofHom (pdRawCoordinateHomotopy k r n s j)

/-- 差座標の指数零かつ対応する一次形式を含まない部分への評価。 -/
def pdRawCoordinateEvaluation : K ⟶ K :=
  𝟙 K - nullHomotopicMap' (pdRawCoordinateHomotopyFamily p k r hp n s)

/-- 一座標の評価は恒等写像とホモトピック。 -/
def pdRawCoordinateEvaluationHomotopy : Homotopy (pdRawCoordinateEvaluation p k r hp n s) (𝟙 K) := by
  let h := (nullHomotopy' (C := K) (D := K) (pdRawCoordinateHomotopyFamily p k r hp n s)).smul (-1 : ℤ)
  simpa only [pdRawCoordinateEvaluation, neg_one_zsmul, zsmul_zero, sub_eq_add_neg, add_zero] using
    (Homotopy.refl (𝟙 K)).add h

private theorem rawD (j : ℕ) : (K).d j (j + 1) = ModuleCat.ofHom (pdRawVertical k r n j) := by
  dsimp only [pdRawDeRhamColumn, CochainComplex.of]
  rw [CochainComplex.of_d]

/-- 零次の差座標評価は係数の定数項を残す。 -/
theorem pdRawCoordinateEvaluation_zero :
    (pdRawCoordinateEvaluation p k r hp n s).f 0 = ModuleCat.ofHom
      (TensorProduct.map (pdRawConstantTerm k r n.len s) LinearMap.id) := by
  dsimp only [pdRawCoordinateEvaluation]
  rw [HomologicalComplex.sub_f_apply,
    nullHomotopicMap'_f_of_not_rel_right (show (ComplexShape.up ℕ).Rel 0 1 from rfl)
      (fun i => show ¬ (ComplexShape.up ℕ).Rel i 0 from by change ¬ i + 1 = 0; omega)]
  rw [rawD]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f w
  let x : pdRawForms k r n 0 := f ⊗ₜ[k] w
  change x - pdRawCoordinateHomotopy k r n s 0 (pdRawVertical k r n 0 x) =
    pdRawConstantTerm k r n.len s f ⊗ₜ[k] w
  have h := DFunLike.congr_fun (pdRawCoordinateHomotopy_zero k r n s) x
  change pdRawCoordinateHomotopy k r n s 0 (pdRawVertical k r n 0 x) =
    (f - pdRawConstantTerm k r n.len s f) ⊗ₜ[k] w at h
  rw [h, TensorProduct.sub_tmul]
  abel

/-- 正次数の差座標評価は係数と外冪の射影のテンソル。 -/
theorem pdRawCoordinateEvaluation_succ (j : ℕ) :
    (pdRawCoordinateEvaluation p k r hp n s).f (j + 1) = ModuleCat.ofHom
      (TensorProduct.map (pdRawConstantTerm k r n.len s)
        (exteriorPower.map (j + 1) (exteriorCoordinateProjection
          ((pdCoordinateBasis k r n).coord (.inr s)) (pdCoordinateBasis k r n (.inr s))))) := by
  dsimp only [pdRawCoordinateEvaluation]
  rw [HomologicalComplex.sub_f_apply,
    nullHomotopicMap'_f (show (ComplexShape.up ℕ).Rel j (j + 1) from rfl)
      (show (ComplexShape.up ℕ).Rel (j + 1) (j + 2) from rfl), rawD, rawD]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f w
  let x : pdRawForms k r n (j + 1) := f ⊗ₜ[k] w
  let W := (basisWedgeOne (pdCoordinateBasis k r n) j (.inr s)).comp
    (basisContract (pdCoordinateBasis k r n) j (.inr s))
  let c := pdRawConstantTerm k r n.len s f
  let y := pdRawVertical k r n j (pdRawCoordinateHomotopy k r n s j x)
  let z := pdRawCoordinateHomotopy k r n s (j + 1) (pdRawVertical k r n (j + 1) x)
  have h := DFunLike.congr_fun (pdRawCoordinateHomotopy_succ k r n s j) x
  change y + z = (f - c) ⊗ₜ[k] w + c ⊗ₜ[k] W w at h
  change x - (z + y) = c ⊗ₜ[k] exteriorPower.map (j + 1)
    (exteriorCoordinateProjection ((pdCoordinateBasis k r n).coord (.inr s))
      (pdCoordinateBasis k r n (.inr s))) w
  rw [add_comm z y, h, exteriorPower_map_coordinateProjection]
  change f ⊗ₜ[k] w - ((f - c) ⊗ₜ[k] w + c ⊗ₜ[k] W w) =
    c ⊗ₜ[k] (w - W w)
  rw [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
  abel

end SerrePositivity.BhattScholze.Prismatic
