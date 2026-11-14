module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCompletedFreeDelta
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineForms

/-!
# Cartier 比較の定義域

## 概要
標数 p の多項式環の完備微分形式を通常の微分形式と同一視する。

## 方針
零元での完備化の単位が環同型になることを用いる。

## 規約
同型は通常の形式を完備微分形式へ送る単位の逆向き。

## 使われ方
多項式の場合の Hodge–Tate 写像と inverse Cartier の照合。
-/

public noncomputable section

open scoped TensorProduct
open SerrePositivity.DerivedCompletion

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) [Fact p.Prime]

private theorem cartierPoly_natCast (T : Type u) :
    (p : MvPolynomial T (cartierBase.{u} p)) = 0 := by
  rw [← map_natCast (MvPolynomial.C : cartierBase p →+* MvPolynomial T (cartierBase p)),
    cartierBase_natCast, map_zero]

variable (T : Type u) [Fintype T] [DecidableEq T]

local notation "P" => DeRham.Poly (cartierBase p) T
local notation "Q" => DeRham.completedPoly (cartierBase p) T p

private def cartierPolyEquiv : Q ≃ₐ[P] P where
  __ := crystallinePrincipalCompletionOfZero (p : P) (cartierPoly_natCast p T)
  commutes' x := crystallinePrincipalCompletionOfZero_unit _ (cartierPoly_natCast p T) x

/-- 完備微分形式の Cartier 比較における定義域を通常の形式で表す。 -/
def cartierCompletedFormsIso (i : ℕ) :
    DeRham.completedForms (cartierBase.{u} p) T p i ≃ₗ[P] DeRham.forms (cartierBase p) T i :=
  (TensorProduct.congr (cartierPolyEquiv p T).toLinearEquiv
    (LinearEquiv.refl P (DeRham.forms (cartierBase p) T i))).trans (TensorProduct.lid P _)

/-- 完備化の単位を通常の微分形式に戻すと元の形式を得る。 -/
@[simp]
theorem cartierCompletedFormsIso_unit (i : ℕ) (ω : DeRham.forms (cartierBase p) T i) :
    cartierCompletedFormsIso p T i (DeRham.completedFormsUnit (cartierBase p) T p i ω) = ω := by
  simp [cartierCompletedFormsIso, DeRham.completedFormsUnit]

/-- 完備微分形式の同一視は外積を保つ。 -/
theorem cartierCompletedFormsIso_wedge {i j : ℕ} (ω : DeRham.completedForms (cartierBase p) T p i)
    (η : DeRham.completedForms (cartierBase p) T p j) :
    cartierCompletedFormsIso p T (i+j) (DeRham.completedWedge (cartierBase p) T p ω η) =
      DeRham.wedge (cartierBase p) T (cartierCompletedFormsIso p T i ω)
        (cartierCompletedFormsIso p T j η) := by
  have unit_surj (n : ℕ) :
      Function.Surjective (DeRham.completedFormsUnit (cartierBase p) T p n) := by
    intro x
    exact ⟨cartierCompletedFormsIso p T n x,
      (cartierCompletedFormsIso p T n).injective (cartierCompletedFormsIso_unit p T n _)⟩
  obtain ⟨ω, rfl⟩ := unit_surj i ω
  obtain ⟨η, rfl⟩ := unit_surj j η
  rw [DeRham.completedWedge_unit]
  simp

/-- 結晶基底上の affine 完備形式を通常の多項式形式と同一視する。 -/
def cartierFormsIso (r i : ℕ) :
    affineForms (crystallineBasePrism.{u} p) r i ≃+
      DeRham.forms (cartierBase.{u} p) (formVars.{u} r) i :=
  (cartierCompletedFormsIso p (formVars.{u} r) i).toAddEquiv

end SerrePositivity.BhattScholze.Prismatic
