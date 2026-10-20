module

public import SerrePositivity.KST.Spectra.SquareBoundaryFamilies

/-!
概要：元の正方形を転置し、左右の実辺を始辺・終辺とする同じ二次元射を得る。
方針：左右境界の実際の制限式を使い、必要な共有辺だけ等式で付け替える。
規約：定値境界を要求しない。使われ方：元の合成・逆向き三角形を保つ高次比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.SquareAdjustment
variable {E : SSet.{u}} {f g : (Δ[1] : SSet.{u}) ⟶ E} (H : SSet.Homotopy f g)

/-- 左右の実辺を結ぶ転置。二次元射は元の正方形の対称写像による前合成。 -/
def transpose : SSet.Homotopy (leftSide ≫ H.h) (rightSide ≫ H.h) :=
  homotopyOfBoundaryRestriction H.h (boundary_restriction H.h)

/-- 転置の左辺は元の始辺そのもの。 -/
lemma transpose_left : leftSide ≫ (transpose H).h = f :=
  (leftSide_swap H.h).trans H.h₀

/-- 転置の右辺も元の終辺そのもの。 -/
lemma transpose_right : rightSide ≫ (transpose H).h = g :=
  (rightSide_swap H.h).trans H.h₁

/-- 共有辺の厳密な照合は転置の実二次元射を変更しない。 -/
def transposeWithEndpoints {l r : (Δ[1] : SSet.{u}) ⟶ E}
    (hl : l = leftSide ≫ H.h) (hr : r = rightSide ≫ H.h) : SSet.Homotopy l r where
  h := (transpose H).h
  h₀ := (transpose H).h₀.trans hl.symm
  h₁ := (transpose H).h₁.trans hr.symm
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

end SerrePositivity.KST.Spectra.SquareAdjustment
