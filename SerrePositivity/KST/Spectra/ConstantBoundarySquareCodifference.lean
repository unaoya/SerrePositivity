module

public import SerrePositivity.KST.Spectra.SpecifiedSquareCodifference

/-!
概要：共通終辺へ至る二つの正方形を、同じ一定境界上で比較する。
方針：両端の同じ定数二単体を指定した相対外ホーンを充填する。
規約：二正方形と比較三角形を保持する。使われ方：二つの交換トレースの自然性比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.SquareAdjustment
variable {E : SSet.{u}} {f g k : (Δ[1] : SSet.{u}) ⟶ E}
  (H : SSet.Homotopy f k) (V : SSet.Homotopy g k) (x y : E _⦋0⦌)

/-- 元の二正方形を、同じ定数二単体の上で保持する共通終辺の比較。 -/
abbrev ConstantBoundaryCodifference := SpecifiedCodifference H V (SSet.const x) (SSet.const y)

/-- 同じ一定境界上で、元の二正方形を保持する外ホーンを相対充填する。 -/
def ConstantBoundaryCodifference.choose [KanComplex E]
    (hH₀ : leftSide ≫ H.h = SSet.const x) (hH₁ : rightSide ≫ H.h = SSet.const y)
    (hV₀ : leftSide ≫ V.h = SSet.const x) (hV₁ : rightSide ≫ V.h = SSet.const y) :
    ConstantBoundaryCodifference H V x y :=
  SpecifiedCodifference.choose H V (SSet.const x) (SSet.const y)
    (by simpa only [SSet.comp_const] using hH₀)
    (by simpa only [SSet.comp_const] using hH₁)
    (by simpa only [SSet.comp_const] using hV₀)
    (by simpa only [SSet.comp_const] using hV₁)

variable (C : ConstantBoundaryCodifference H V x y)

/-- 比較正方形の左辺全体も、指定した同じ頂点で一定。 -/
lemma ConstantBoundaryCodifference.start : leftSide ≫ C.homotopy.h = SSet.const x := by
  have hb := SpecifiedCodifference.boundary H V (SSet.const x) (SSet.const y) C
  simp only [SSet.comp_const] at hb
  exact (sides_of_boundary_restriction C.homotopy.h hb).1

/-- 比較正方形の右辺全体も、指定した同じ頂点で一定。 -/
lemma ConstantBoundaryCodifference.finish : rightSide ≫ C.homotopy.h = SSet.const y := by
  have hb := SpecifiedCodifference.boundary H V (SSet.const x) (SSet.const y) C
  simp only [SSet.comp_const] at hb
  exact (sides_of_boundary_restriction C.homotopy.h hb).2

end SerrePositivity.KST.Spectra.SquareAdjustment
