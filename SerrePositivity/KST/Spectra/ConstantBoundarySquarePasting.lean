module

public import SerrePositivity.KST.Spectra.SpecifiedSquarePasting

/-!
概要：同じ一定な左右境界を持つ二つの実正方形を、指定した定数二単体の上で貼る。
方針：既存の相対内ホーン充填に、両端の同じ定数三角形を渡す。
規約：入力二辺と合成三角形を保持する。使われ方：交換区間のトレースと自然性の合成。
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
  (H : SSet.Homotopy f g) (V : SSet.Homotopy g k) (x y : E _⦋0⦌)

/-- 同じ一定境界上の指定三角形を保持する、元の二つの正方形の合成。 -/
abbrev ConstantBoundaryPasting := SpecifiedPasting H V (SSet.const x) (SSet.const y)

/-- 一定な左右境界には同じ定数二単体を指定して、相対ホーンを充填する。 -/
def ConstantBoundaryPasting.choose [KanComplex E]
    (hH₀ : leftSide ≫ H.h = SSet.const x) (hH₁ : rightSide ≫ H.h = SSet.const y)
    (hV₀ : leftSide ≫ V.h = SSet.const x) (hV₁ : rightSide ≫ V.h = SSet.const y) :
    ConstantBoundaryPasting H V x y :=
  SpecifiedPasting.choose H V (SSet.const x) (SSet.const y)
    (by simpa only [SSet.comp_const] using hH₀)
    (by simpa only [SSet.comp_const] using hH₁)
    (by simpa only [SSet.comp_const] using hV₀)
    (by simpa only [SSet.comp_const] using hV₁)

variable (C : ConstantBoundaryPasting H V x y)

/-- 合成正方形の左辺全体も、指定した同じ頂点で一定。 -/
lemma ConstantBoundaryPasting.start : leftSide ≫ C.homotopy.h = SSet.const x := by
  have hb := SpecifiedPasting.boundary H V (SSet.const x) (SSet.const y) C
  simp only [SSet.comp_const] at hb
  exact (sides_of_boundary_restriction C.homotopy.h hb).1

/-- 合成正方形の右辺全体も、指定した同じ頂点で一定。 -/
lemma ConstantBoundaryPasting.finish : rightSide ≫ C.homotopy.h = SSet.const y := by
  have hb := SpecifiedPasting.boundary H V (SSet.const x) (SSet.const y) C
  simp only [SSet.comp_const] at hb
  exact (sides_of_boundary_restriction C.homotopy.h hb).2

end SerrePositivity.KST.Spectra.SquareAdjustment
