module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineForms
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCompletedFreeDelta

/-!
# 結晶的な affine 完備形式と元の通常形式

## 概要
選択生成元が p の場合、元の完備形式を通常の多項式形式に、単位と外積を保って同定する。

## 方針
剰余で p が零であることと、元の零元完備化の標準同型を使う。

## 規約
一般の結晶 HT 比較を仮定しない。ここで比較するのは標準写像の定義域の形式だけである。

## 使われ方
特定の Zp 係数射の標準 HT 写像で、形式の通常の係数変更を計算する。
-/

public noncomputable section
universe u
open scoped TensorProduct
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hg : P.generator = (p : A))
include hg

/-- 結晶的な選択生成元 p は、元の基底剰余環で零になる。 -/
theorem crystallineResidue_p_zero : (p : A ⧸ P.ideal) = 0 := by
  change Ideal.Quotient.mk P.ideal (p : A) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have h : P.generator ∈ P.ideal := Ideal.subset_span rfl
  exact hg ▸ h

/-- 元の剰余係数上の多項式環でも p は零。 -/
theorem crystallinePolynomial_p_zero (T : Type u) : (p : MvPolynomial T (A ⧸ P.ideal)) = 0 := by
  rw [← map_natCast (MvPolynomial.C : (A ⧸ P.ideal) →+* MvPolynomial T (A ⧸ P.ideal)),
    crystallineResidue_p_zero P hg, map_zero]

private def crystallinePolyCompletionEquiv (T : Type u) [Fintype T] [DecidableEq T] :
    DeRham.completedPoly (A ⧸ P.ideal) T p ≃ₐ[DeRham.Poly (A ⧸ P.ideal) T]
      DeRham.Poly (A ⧸ P.ideal) T where
  __ := crystallinePrincipalCompletionOfZero (p : DeRham.Poly (A ⧸ P.ideal) T)
    (crystallinePolynomial_p_zero P hg T)
  commutes' x := crystallinePrincipalCompletionOfZero_unit _ (crystallinePolynomial_p_zero P hg T) x

variable (T : Type u) [Fintype T] [DecidableEq T]
local notation "k" => A ⧸ P.ideal
local notation "R" => DeRham.Poly k T

/-- 元の結晶的な完備形式の、通常形式への標準線形同型。 -/
def crystallineCompletedFormsReductionIso (i : ℕ) :
    DeRham.completedForms k T p i ≃ₗ[R] DeRham.forms k T i :=
  (TensorProduct.congr (crystallinePolyCompletionEquiv P hg T).toLinearEquiv
    (LinearEquiv.refl R (DeRham.forms k T i))).trans (TensorProduct.lid R _)

/-- この同型は、元の通常形式の完備化単位を戻す。 -/
@[simp] theorem crystallineCompletedFormsReductionIso_unit (i : ℕ) (x : DeRham.forms k T i) :
    crystallineCompletedFormsReductionIso P hg T i (DeRham.completedFormsUnit k T p i x) = x := by
  simp [crystallineCompletedFormsReductionIso, DeRham.completedFormsUnit]

/-- 元の同一視は、元の完備外積と通常外積を保つ。 -/
theorem crystallineCompletedFormsReductionIso_wedge {i j : ℕ}
    (x : DeRham.completedForms k T p i) (y : DeRham.completedForms k T p j) :
    crystallineCompletedFormsReductionIso P hg T (i + j) (DeRham.completedWedge k T p x y) =
      DeRham.wedge k T (crystallineCompletedFormsReductionIso P hg T i x)
        (crystallineCompletedFormsReductionIso P hg T j y) := by
  have hu (n : ℕ) : Function.Surjective (DeRham.completedFormsUnit k T p n) := by
    intro z
    exact ⟨crystallineCompletedFormsReductionIso P hg T n z,
      (crystallineCompletedFormsReductionIso P hg T n).injective
        (crystallineCompletedFormsReductionIso_unit P hg T n _)⟩
  obtain ⟨x, rfl⟩ := hu i x
  obtain ⟨y, rfl⟩ := hu j y
  rw [DeRham.completedWedge_unit]
  simp

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
