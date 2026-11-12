module
public import SerrePositivity.KST.SConstruction.TriangleLeftCancellationOutputComparison

/-! # 元の全基底比較を保つ始辺消去の全出力円柱比較
概要：fibration に沿う全四面体比較の持ち上げを、全出力円柱の実比較へ戻す。
方針：指定三面を保つ同じ持ち上げの零面を取り、固定した退化下面と貼る。
規約：元の全基底比較の零面と指定三面を保持し、定数基底への置換をしない。
使われ方：単射源構造射の制限に沿い最後の消去選択を全境界固定で揃える。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
variable {E B : SSet.{u}} {x y z : E _⦋0⦌}
  {a : E.Edge x y} {b d : E.Edge y z} {c : E.Edge x z}
  (T : SSet.Edge.CompStruct a b c) (U : SSet.Edge.CompStruct a d c)
  (v w : (triangleLeftCancellationChoices T U) _⦋0⦌)
  (p : E ⟶ B) [Fibration p]
  (H : SSet.Homotopy (triangleLeftCancellationAt T U v ≫ p)
    (triangleLeftCancellationAt T U w ≫ p))
  (hr : ((horn 3 (0 : Fin 4)).ι ▷ (Δ[1] : SSet.{u})) ≫ H.h =
    fst (Λ[3, 0] : SSet.{u}) Δ[1] ≫ triangleLeftCancellationHorn T U ≫ p)

/-- 元の全基底比較を保持する同じ四面体持ち上げから、全出力円柱比較を得る。 -/
def triangleLeftCancellationCylinderComparisonOver :=
  triangleLeftCancellationOutputComparison T U v w
    (triangleLeftCancellationComparisonOverData T U v w p H hr).val
    (triangleLeftCancellationComparisonOverData_relative T U v w p H hr)

/-- 入力全境界と元の比較時刻の両端を全高次比較時刻で同時に固定する。 -/
lemma triangleLeftCancellationCylinderComparisonOver_relative :
    (fullCylinderBoundaryInclusion (SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫
        (triangleLeftCancellationCylinderComparisonOver T U v w p H hr).h =
      fst (fullCylinderBoundary (SSet.boundary 1).ι) Δ[1] ≫
        fullCylinderBoundaryInclusion (SSet.boundary 1).ι ≫
          (triangleLeftCancellationCylinder T U v).homotopy.h :=
  triangleLeftCancellationOutputComparison_relative _ _ _ _ _ _

/-- 持ち上げた元の全四面体比較の零面を、全出力円柱比較の上面に保持する。 -/
lemma triangleLeftCancellationCylinderComparisonOver_upper :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ▷ (Δ[1] : SSet.{u})) ≫
        (triangleLeftCancellationCylinderComparisonOver T U v w p H hr).h =
      (stdSimplex.δ 0 ▷ (Δ[1] : SSet.{u})) ≫
        (triangleLeftCancellationComparisonOverData T U v w p H hr).val.h :=
  triangleLeftCancellationOutputComparison_upper _ _ _ _ _ _

/-- 全出力円柱比較の上面の射影は、元の全基底比較の同じ零面そのもの。 -/
lemma triangleLeftCancellationCylinderComparisonOver_upper_projection :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ▷ (Δ[1] : SSet.{u})) ≫
        (triangleLeftCancellationCylinderComparisonOver T U v w p H hr).h ≫ p =
      (stdSimplex.δ 0 ▷ (Δ[1] : SSet.{u})) ≫ H.h := by
  rw [← Category.assoc, triangleLeftCancellationCylinderComparisonOver_upper, Category.assoc,
    triangleLeftCancellationComparisonOverData_projection]

/-- 全基底円柱の両三角形を指定すれば、出力した全高次円柱も同じ全基底像を保つ。 -/
lemma triangleLeftCancellationCylinderComparisonOver_projection
    (q : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) ⊗ Δ[1] ⟶ B)
    (hu : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ▷ (Δ[1] : SSet.{u})) ≫ q =
      (stdSimplex.δ 0 ▷ (Δ[1] : SSet.{u})) ≫ H.h)
    (hl : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ▷ (Δ[1] : SSet.{u})) ≫ q =
      fst (Δ[2] : SSet.{u}) Δ[1] ≫
        SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.compId b).simplex ≫ p) :
    (triangleLeftCancellationCylinderComparisonOver T U v w p H hr).h ≫ p = q := by
  apply triangleLeftCancellationCylinderComparisonFromTriangle_projection T U v w
    (triangleLeftCancellationOutputTriangleComparison T U v w
      (triangleLeftCancellationComparisonOverData T U v w p H hr).val)
    (triangleLeftCancellationOutputTriangleComparison_edge T U v w
      (triangleLeftCancellationComparisonOverData T U v w p H hr).val
      (triangleLeftCancellationComparisonOverData_relative T U v w p H hr)) p q
  · rw [triangleLeftCancellationOutputTriangleComparison_h, Category.assoc,
      triangleLeftCancellationComparisonOverData_projection]
    exact hu
  · exact hl

end SerrePositivity.KST.SConstruction
