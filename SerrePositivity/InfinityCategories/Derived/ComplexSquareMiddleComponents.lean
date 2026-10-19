module
public import SerrePositivity.InfinityCategories.Derived.ComplexSquareMiddleHomotopy
public import SerrePositivity.InfinityCategories.Stable.SquareUpperCornerEvaluation

/-! # 中間対象変更の両端成分

概要：右下の中間対象だけを変更する正方形比較は始点と終点で恒等射になる。
方針：上三角形の定値性を、関手圏の h の両端評価へ移す。
規約：端点表示は Arrow に含める。使われ方：D7 の cofiber から suspension の合成比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
universe u
namespace SerrePositivity.InfinityCategories.ComplexSquareData
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve
open scoped Simplicial
variable {S : Type u} [CommRing S] {A B B' C D : Complex S}
variable (s : ComplexSquareData A B C D) (m : B ⟶ B') (r : B' ⟶ D) (hr : m ≫ r = s.right)

/-- 右下の中間対象を変更する比較の始点・終点成分は恒等射。 -/
lemma changeBottomMiddleHomotopy_corner_arrow (i : Fin 2) :
    Arrow.mk ((squareDiagramHoEvaluation (dgNerve S (Complex S)) i i).map
      (SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (s.changeBottomMiddleHomotopy m r hr)))) =
      Arrow.mk (𝟙 (squareHoVertex s.square i i)) := by
  apply squareUpperConstantHomotopy_corner_arrow
  exact (s.changeBottomMiddleHomotopy_upper m r hr).trans
    (congrArg (fun q => CartesianMonoidalCategory.fst (Δ[2] : SSet.{u + 1}) Δ[1] ≫ q)
      s.square_upper.symm)

end SerrePositivity.InfinityCategories.ComplexSquareData
