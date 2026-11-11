module
public import SerrePositivity.KST.SConstruction.TracedTripleGeometricStageComparison
public import SerrePositivity.KST.SConstruction.TriangleLeftCancellationCylinderComparison

/-! # 元の raw 各段の最後の消去選択を全境界固定で比較する
概要：元の六対角面消去の他の全データを保ち、最後の始辺消去の二選択を実比較する。
方針：同じ全二合成面を持つ消去四面体の全比較を、出力した全円柱比較へ戻す。
規約：入力全境界と比較時刻の両端を同時に固定する。隣接段適合全体とは数えない。
使われ方：元の高次 prism と同時に消去選択を揃える相対構成の最後の工程。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z) (n : ℕ)
  (v : (triangleLeftCancellationChoices
    (monicKTracedTripleGeometricStagePasting F f g h n).transported
    (monicKTracedTripleGeometricStagePasting F f g h n).bottom.triangle) _⦋0⦌)

/-- 最後の消去だけを指定の同じ全四面体に替えた、同じ両辺の全端点固定円柱。 -/
def monicKTracedTripleGeometricPrefixCylinder :=
  triangleLeftCancellationCylinder
    (monicKTracedTripleGeometricStagePasting F f g h n).transported
    (monicKTracedTripleGeometricStagePasting F f g h n).bottom.triangle v

/-- 元の raw 段全円柱から、指定した最後の消去による全円柱への実高次比較。 -/
def monicKTracedTripleGeometricPrefixComparison :=
  triangleLeftCancellationCylinderComparison
    (monicKTracedTripleGeometricStagePasting F f g h n).transported
    (monicKTracedTripleGeometricStagePasting F f g h n).bottom.triangle
    (monicKTracedTripleGeometricStagePasting F f g h n).prefixChoice v

/-- 元の raw 段の最後の消去比較は、入力境界と比較時刻の両端を全時刻固定する。 -/
lemma monicKTracedTripleGeometricPrefixComparison_relative :
    (fullCylinderBoundaryInclusion (SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedTripleGeometricPrefixComparison F f g h n v).h =
      fst (fullCylinderBoundary (SSet.boundary 1).ι) Δ[1] ≫
        fullCylinderBoundaryInclusion (SSet.boundary 1).ι ≫
          (monicKTracedTripleGeometricRawStageComparison F f g h n).homotopy.h := by
  exact (triangleLeftCancellationCylinderComparison_relative
    (monicKTracedTripleGeometricStagePasting F f g h n).transported
    (monicKTracedTripleGeometricStagePasting F f g h n).bottom.triangle
    (monicKTracedTripleGeometricStagePasting F f g h n).prefixChoice v).trans
      (congrArg (fun q => fst (fullCylinderBoundary (SSet.boundary 1).ι) Δ[1] ≫
        fullCylinderBoundaryInclusion (SSet.boundary 1).ι ≫ q)
        (monicKTracedTripleGeometricRawStageComparison_h F f g h n).symm)

/-- 元の全消去四面体比較の残面を、同じ全出力円柱比較の上面へ厳密に保持する。 -/
lemma monicKTracedTripleGeometricPrefixComparison_upper :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedTripleGeometricPrefixComparison F f g h n v).h =
      (triangleLeftCancellationTriangleComparison
        (monicKTracedTripleGeometricStagePasting F f g h n).transported
        (monicKTracedTripleGeometricStagePasting F f g h n).bottom.triangle
        (monicKTracedTripleGeometricStagePasting F f g h n).prefixChoice v).h :=
  triangleLeftCancellationCylinderComparison_upper _ _ _ _

end SerrePositivity.KST.SConstruction
