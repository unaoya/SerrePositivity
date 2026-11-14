module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDColumnCoordinateEvaluation
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedDerivation
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDColumnContraction
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumn
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRow

/-!
# 完備分冪 de Rham 列の差座標の収縮

## 概要
完備分冪係数上で、一つの差座標を消す鎖ホモトピーを構成する。

## 方針
分冪積分と定数項を完備化する。係数上の反交換子の等式を完備化の単位で確かめ、
既存の外冪の内部積の公式を適用する。

## 規約
p の像が零であることは仮定しない。

## 使われ方
BS 著者版 Theorems 5.2・6.4 の完備 pd de Rham 比較。
-/

public noncomputable section

open CategoryTheory HomologicalComplex Homotopy SerrePositivity.DerivedCompletion
  SerrePositivity.DeRham
open scoped TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) (k : Type u) [CommRing k]

private theorem completionLinearMap_id (A : Type u) [CommRing A] [Algebra k A] :
    principalCompletionLinearMap k p (LinearMap.id (R := k) (M := A)) = LinearMap.id := by
  apply principalCompletionLinearMap_ext k p (completedRing_isModuleComplete k p)
  intro a
  rw [principalCompletionLinearMap_unit]
  rfl

private theorem completionLinearMap_sub {A : Type u} [CommRing A] [Algebra k A]
    (f g : A →ₗ[k] A) :
    principalCompletionLinearMap k p (f - g) =
      principalCompletionLinearMap k p f - principalCompletionLinearMap k p g := by
  apply principalCompletionLinearMap_ext k p (completedRing_isModuleComplete k p)
  intro a
  simp only [LinearMap.sub_apply]
  rw [principalCompletionLinearMap_unit k p (f - g) a, principalCompletionLinearMap_unit k p f a,
    principalCompletionLinearMap_unit k p g a]
  rw [LinearMap.sub_apply]
  exact map_sub (principalCompletionRingCatUnit p (CommRingCat.of A)).hom (f a) (g a)

variable (r m : ℕ)

private abbrev integral (s : Fin r × Fin m) : pdTerm p k r m →ₗ[k] pdTerm p k r m :=
  principalCompletionLinearMap k p (A := pdRaw k r m) (B := pdRaw k r m) (pdRawIntegral k r m s)

/-- 完備分冪係数で指定した差座標の定数項を残す。 -/
abbrev pdCompletedConstantTerm (s : Fin r × Fin m) : pdTerm p k r m →ₗ[k] pdTerm p k r m :=
  principalCompletionLinearMap k p (A := pdRaw k r m) (B := pdRaw k r m) (pdRawConstantTerm k r m s)

private theorem pdCompletedPartial_integral (s : Fin r × Fin m) :
    (pdCompletedPartial p k r m (.inr s)).comp (integral p k r m s) = LinearMap.id := by
  change (principalCompletionLinearMap k p (A := pdRaw k r m) (B := pdRaw k r m)
    (pdRawPartial k r m (.inr s))).comp
    (principalCompletionLinearMap k p (A := pdRaw k r m) (B := pdRaw k r m)
      (pdRawIntegral k r m s)) = LinearMap.id
  rw [← principalCompletionLinearMap_comp, pdRawPartial_integral, completionLinearMap_id]

private theorem pdCompletedIntegral_partial (s : Fin r × Fin m) :
    (integral p k r m s).comp (pdCompletedPartial p k r m (.inr s)) =
      LinearMap.id - pdCompletedConstantTerm p k r m s := by
  change (principalCompletionLinearMap k p (A := pdRaw k r m) (B := pdRaw k r m)
    (pdRawIntegral k r m s)).comp
    (principalCompletionLinearMap k p (A := pdRaw k r m) (B := pdRaw k r m)
      (pdRawPartial k r m (.inr s))) = _
  rw [← principalCompletionLinearMap_comp, pdRawIntegral_partial,
    completionLinearMap_sub, completionLinearMap_id]

private theorem pdCompletedPartial_integral_comm (s : Fin r × Fin m) (t : pdCoordinates r m)
    (h : t ≠ .inr s) :
    (pdCompletedPartial p k r m t).comp (integral p k r m s) =
      (integral p k r m s).comp (pdCompletedPartial p k r m t) := by
  change (principalCompletionLinearMap k p (A := pdRaw k r m) (B := pdRaw k r m)
    (pdRawPartial k r m t)).comp
    (principalCompletionLinearMap k p (A := pdRaw k r m) (B := pdRaw k r m)
      (pdRawIntegral k r m s)) =
    (principalCompletionLinearMap k p (A := pdRaw k r m) (B := pdRaw k r m)
      (pdRawIntegral k r m s)).comp
      (principalCompletionLinearMap k p (A := pdRaw k r m) (B := pdRaw k r m)
        (pdRawPartial k r m t))
  rw [← principalCompletionLinearMap_comp, ← principalCompletionLinearMap_comp,
    pdRawPartial_integral_comm k r m s t h]

variable (n : SimplexCategory)

private theorem verticalD_eq_tensorExteriorD (j : ℕ) :
    (pdVerticalD p k r n j).hom =
      tensorExteriorD (pdCoordinateBasis k r n) (pdCompletedPartial p k r n.len) j := by
  unfold pdVerticalD tensorExteriorD basisWedgeOne pdCoordinateOne
  simp only [pdCoordinateBasis_apply]
  rfl

local notation "K" => pdDeRhamColumn p k r n

/-- 完備列で一つの差座標を消す収縮。 -/
def pdCompletedCoordinateHomotopy (s : Fin r × Fin n.len) (j : ℕ) :
    (pdRow p k r (j + 1)).obj n →ₗ[k] (pdRow p k r j).obj n :=
  tensorExteriorH (pdCoordinateBasis k r n) (integral p k r n.len s) (.inr s) j

private theorem completedCoordinateHomotopy_zero (s : Fin r × Fin n.len) :
    (pdCompletedCoordinateHomotopy p k r n s 0).comp (pdVerticalD p k r n 0).hom =
      TensorProduct.map (LinearMap.id - pdCompletedConstantTerm p k r n.len s) LinearMap.id := by
  rw [pdCompletedCoordinateHomotopy, verticalD_eq_tensorExteriorD, tensorExteriorH_D_zero,
    pdCompletedIntegral_partial]

private theorem completedCoordinateHomotopy_succ (s : Fin r × Fin n.len) (j : ℕ) :
    (pdVerticalD p k r n j).hom.comp (pdCompletedCoordinateHomotopy p k r n s j) +
      (pdCompletedCoordinateHomotopy p k r n s (j + 1)).comp (pdVerticalD p k r n (j + 1)).hom =
      TensorProduct.map (LinearMap.id - pdCompletedConstantTerm p k r n.len s) LinearMap.id +
      TensorProduct.map (pdCompletedConstantTerm p k r n.len s)
        ((basisWedgeOne (pdCoordinateBasis k r n) j (.inr s)).comp
          (basisContract (pdCoordinateBasis k r n) j (.inr s))) := by
  rw [pdCompletedCoordinateHomotopy, pdCompletedCoordinateHomotopy, verticalD_eq_tensorExteriorD,
    verticalD_eq_tensorExteriorD, tensorExteriorD_H _ _ _ _
      (pdCompletedPartial_integral_comm p k r n.len s),
    pdCompletedPartial_integral, pdCompletedIntegral_partial]
  have h : LinearMap.id - (LinearMap.id - pdCompletedConstantTerm p k r n.len s) =
      pdCompletedConstantTerm p k r n.len s := by abel
  rw [h]

variable (s : Fin r × Fin n.len)

private def completedCoordinateHomotopyFamily (i j : ℕ) (h : (ComplexShape.up ℕ).Rel j i) :
    (K).X i ⟶ (K).X j := by
  have hi : j + 1 = i := h
  subst i
  exact ModuleCat.ofHom (pdCompletedCoordinateHomotopy p k r n s j)

/-- 差座標の指数零かつ対応する一次形式を含まない部分への評価。 -/
def pdCompletedCoordinateEvaluation : K ⟶ K :=
  𝟙 K - nullHomotopicMap' (completedCoordinateHomotopyFamily p k r n s)

/-- 一座標の評価は恒等写像とホモトピック。 -/
def pdCompletedCoordinateEvaluationHomotopy :
    Homotopy (pdCompletedCoordinateEvaluation p k r n s) (𝟙 K) := by
  let h := (nullHomotopy' (C := K) (D := K)
    (completedCoordinateHomotopyFamily p k r n s)).smul (-1 : ℤ)
  simpa only [pdCompletedCoordinateEvaluation, neg_one_zsmul, zsmul_zero, sub_eq_add_neg,
    add_zero] using
    (Homotopy.refl (𝟙 K)).add h

private theorem completedD (j : ℕ) : (K).d j (j + 1) = pdVerticalD p k r n j := by
  dsimp only [pdDeRhamColumn]
  rw [CochainComplex.of_d]

/-- 零次の差座標評価は係数の定数項を残す。 -/
private theorem pdCompletedCoordinateEvaluation_zero :
    (pdCompletedCoordinateEvaluation p k r n s).f 0 = ModuleCat.ofHom
      (TensorProduct.map (pdCompletedConstantTerm p k r n.len s) LinearMap.id) := by
  dsimp only [pdCompletedCoordinateEvaluation]
  rw [HomologicalComplex.sub_f_apply,
    nullHomotopicMap'_f_of_not_rel_right (show (ComplexShape.up ℕ).Rel 0 1 from rfl)
      (fun i => show ¬ (ComplexShape.up ℕ).Rel i 0 from by change ¬ i + 1 = 0; omega)]
  rw [completedD]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f w
  change pdTerm p k r n.len at f
  change ⋀[k]^0 (CopyModule k r n) at w
  let x := f ⊗ₜ[k] w
  let y : pdTerm p k r n.len ⊗[k] (⋀[k]^0 (CopyModule k r n)) :=
    pdCompletedCoordinateHomotopy p k r n s 0 ((pdVerticalD p k r n 0).hom x)
  change x - y = pdCompletedConstantTerm p k r n.len s f ⊗ₜ[k] w
  have h := DFunLike.congr_fun (completedCoordinateHomotopy_zero p k r n s) x
  change y = (f - pdCompletedConstantTerm p k r n.len s f) ⊗ₜ[k] w at h
  rw [h, TensorProduct.sub_tmul]
  abel

/-- 正次数の差座標評価は係数と外冪の射影のテンソル。 -/
private theorem pdCompletedCoordinateEvaluation_succ (j : ℕ) :
    (pdCompletedCoordinateEvaluation p k r n s).f (j + 1) = ModuleCat.ofHom
      (TensorProduct.map (pdCompletedConstantTerm p k r n.len s)
        (exteriorPower.map (j + 1) (exteriorCoordinateProjection
          ((pdCoordinateBasis k r n).coord (.inr s)) (pdCoordinateBasis k r n (.inr s))))) := by
  dsimp only [pdCompletedCoordinateEvaluation]
  rw [HomologicalComplex.sub_f_apply,
    nullHomotopicMap'_f (show (ComplexShape.up ℕ).Rel j (j + 1) from rfl)
      (show (ComplexShape.up ℕ).Rel (j + 1) (j + 2) from rfl), completedD, completedD]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f w
  change pdTerm p k r n.len at f
  change ⋀[k]^(j + 1) (CopyModule k r n) at w
  let x := f ⊗ₜ[k] w
  let W := (basisWedgeOne (pdCoordinateBasis k r n) j (.inr s)).comp
    (basisContract (pdCoordinateBasis k r n) j (.inr s))
  let c := pdCompletedConstantTerm p k r n.len s f
  let y : pdTerm p k r n.len ⊗[k] (⋀[k]^(j + 1) (CopyModule k r n)) :=
    (pdVerticalD p k r n j).hom (pdCompletedCoordinateHomotopy p k r n s j x)
  let z : pdTerm p k r n.len ⊗[k] (⋀[k]^(j + 1) (CopyModule k r n)) :=
    pdCompletedCoordinateHomotopy p k r n s (j + 1) ((pdVerticalD p k r n (j + 1)).hom x)
  have h := DFunLike.congr_fun (completedCoordinateHomotopy_succ p k r n s j) x
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
