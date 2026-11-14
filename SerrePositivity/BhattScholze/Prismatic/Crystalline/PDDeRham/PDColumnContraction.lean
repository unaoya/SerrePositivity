module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDRawDeRhamColumn
public import SerrePositivity.CommutativeAlgebra.DividedPowers.FreeDPIntegral
public import SerrePositivity.CommutativeAlgebra.DeRham.ExteriorTensorContraction
import all SerrePositivity.CommutativeAlgebra.DeRham.ExteriorTensorContraction
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDRawDeRhamColumn
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawDifferential
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumn
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRow

/-!
# pd 列の差座標の収縮

## 概要
一つの差座標について、分冪積分と外冪の内部積を組み合わせる。

## 方針
同じ差座標の偏微分と積分の合成を計算し、他の座標での可換性を使う。

## 規約
差座標の定数項は指数零の分冪単項式で表す。

## 使われ方
pd de Rham 列の Poincaré 補題。
-/

public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

open SerrePositivity.DeRham

variable (k : Type u) [CommRing k] (r n : ℕ)

local notation "S" => (Fin r × Fin n)

/-- 一つの差座標の分冪積分。 -/
def pdRawIntegral (s : S) : pdRaw k r n →ₗ[k] pdRaw k r n :=
  TensorProduct.map LinearMap.id (freeDPIntegral s)

/-- 指定した差座標の定数項を残す。 -/
def pdRawConstantTerm (s : S) : pdRaw k r n →ₗ[k] pdRaw k r n :=
  TensorProduct.map LinearMap.id (freeDPConstantTerm s)

private theorem pdRawPartial_integral (s : S) :
    (pdRawPartial k r n (.inr s)).comp (pdRawIntegral k r n s) = LinearMap.id := by
  apply TensorProduct.ext'
  intro f g
  simp only [pdRawIntegral, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    partial_inr_tmul, freeDPPartial_integral]

private theorem pdRawIntegral_partial (s : S) :
    (pdRawIntegral k r n s).comp (pdRawPartial k r n (.inr s)) =
      LinearMap.id - pdRawConstantTerm k r n s := by
  apply TensorProduct.ext'
  intro f g
  simp only [pdRawIntegral, pdRawConstantTerm, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, partial_inr_tmul, freeDPIntegral_partial, LinearMap.sub_apply,
    TensorProduct.tmul_sub]

private theorem pdRawPartial_integral_comm (s : S) (t : pdCoordinates r n) (h : t ≠ .inr s) :
    (pdRawPartial k r n t).comp (pdRawIntegral k r n s) =
      (pdRawIntegral k r n s).comp (pdRawPartial k r n t) := by
  apply TensorProduct.ext'
  intro f g
  rcases t with t | t
  · simp only [pdRawIntegral, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
      partial_inl_tmul]
  · simp only [pdRawIntegral, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
      partial_inr_tmul, freeDPPartial_integral_comm (fun h' => h (congrArg Sum.inr h'))]

variable (m : SimplexCategory)

private theorem pdRawVertical_eq_tensorExteriorD (j : ℕ) :
    pdRawVertical k r m j = tensorExteriorD (pdCoordinateBasis k r m)
      (pdRawPartial k r m.len) j := by
  unfold pdRawVertical tensorExteriorD basisWedgeOne pdCoordinateOne
  simp only [pdCoordinateBasis_apply]

/-- 差座標の収縮は分冪積分と内部積のテンソル。 -/
def pdRawCoordinateHomotopy (s : Fin r × Fin m.len) (j : ℕ) :
    pdRawForms k r m (j+1) →ₗ[k] pdRawForms k r m j :=
  tensorExteriorH (pdCoordinateBasis k r m) (pdRawIntegral k r m.len s) (.inr s) j

/-- 零次の pd 形式では、座標の収縮で定数項を除いた部分が得られる。 -/
theorem pdRawCoordinateHomotopy_zero (s : Fin r × Fin m.len) :
    (pdRawCoordinateHomotopy k r m s 0).comp (pdRawVertical k r m 0) =
      TensorProduct.map (LinearMap.id - pdRawConstantTerm k r m.len s) LinearMap.id := by
  rw [pdRawCoordinateHomotopy, pdRawVertical_eq_tensorExteriorD, tensorExteriorH_D_zero,
    pdRawIntegral_partial]

/-- 正次数での pd de Rham 微分と一座標の収縮の反交換子。 -/
theorem pdRawCoordinateHomotopy_succ (s : Fin r × Fin m.len) (j : ℕ) :
    (pdRawVertical k r m j).comp (pdRawCoordinateHomotopy k r m s j) +
      (pdRawCoordinateHomotopy k r m s (j+1)).comp (pdRawVertical k r m (j+1)) =
      TensorProduct.map (LinearMap.id - pdRawConstantTerm k r m.len s) LinearMap.id +
      TensorProduct.map (pdRawConstantTerm k r m.len s)
        ((basisWedgeOne (pdCoordinateBasis k r m) j (.inr s)).comp
          (basisContract (pdCoordinateBasis k r m) j (.inr s))) := by
  rw [pdRawCoordinateHomotopy, pdRawCoordinateHomotopy, pdRawVertical_eq_tensorExteriorD,
    pdRawVertical_eq_tensorExteriorD, tensorExteriorD_H _ _ _ _
      (pdRawPartial_integral_comm k r m.len s),
    pdRawPartial_integral, pdRawIntegral_partial]
  have h : LinearMap.id - (LinearMap.id - pdRawConstantTerm k r m.len s) =
      pdRawConstantTerm k r m.len s := by abel
  rw [h]

end SerrePositivity.BhattScholze.Prismatic
