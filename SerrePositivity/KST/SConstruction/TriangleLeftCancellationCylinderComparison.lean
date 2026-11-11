module
public import SerrePositivity.KST.SConstruction.TriangleLeftCancellationComparison
public import SerrePositivity.KST.SConstruction.SquareTriangleFixedHomotopy

/-! # 始辺消去の同じ全三角形比較を全境界固定の出力円柱比較へ戻す
概要：消去四面体の残面の全比較を、出力した全円柱の実高次比較にする。
方針：動く上面と固定した退化下面を、同じ全対角比較に沿って貼る。
規約：元の全残面比較を保持し、入力境界と円柱時刻の両端を同時に固定する。
使われ方：六対角面の最後の消去の選択を、元の全高次 prism に沿って比較する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {E : SSet.{u}} {x y z : E _⦋0⦌}
  {a : E.Edge x y} {b d : E.Edge y z} {c : E.Edge x z}
  (T : SSet.Edge.CompStruct a b c) (U : SSet.Edge.CompStruct a d c)
  (v w : (triangleLeftCancellationChoices T U) _⦋0⦌)
  (H : SSet.Homotopy
    (SSet.yonedaEquiv.symm (triangleLeftCancellationTriangle T U v).simplex)
    (SSet.yonedaEquiv.symm (triangleLeftCancellationTriangle T U w).simplex))
  (hr : ∀ i : Fin 3, (stdSimplex.δ i ▷ (Δ[1] : SSet.{u})) ≫ H.h =
    fst (Δ[1] : SSet.{u}) Δ[1] ≫ stdSimplex.δ i ≫
      SSet.yonedaEquiv.symm (triangleLeftCancellationTriangle T U v).simplex)

/-- 元の同じ全残面比較を、出力円柱の上面表示へ合わせる。 -/
def triangleLeftCancellationUpperComparison :=
  familyHomotopyEndpointTransport H
    (ThreeEdgeTransport.square_upper (triangleLeftCancellationTransport T U v))
    (ThreeEdgeTransport.square_upper (triangleLeftCancellationTransport T U w)).symm

/-- 出力円柱の下面は、元の同じ退化三角形に全比較時刻で固定する。 -/
def triangleLeftCancellationLowerComparison :=
  familyHomotopyEndpointTransport
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.compId b).simplex))
    (ThreeEdgeTransport.square_lower (triangleLeftCancellationTransport T U v))
    (ThreeEdgeTransport.square_lower (triangleLeftCancellationTransport T U w)).symm

include hr

/-- 元の上面比較の全三辺を厳密に固定する。 -/
lemma triangleLeftCancellationUpperComparison_edge (i : Fin 3) :
    (stdSimplex.δ i ▷ (Δ[1] : SSet.{u})) ≫
        (triangleLeftCancellationUpperComparison T U v w H).h =
      fst (Δ[1] : SSet.{u}) Δ[1] ≫ stdSimplex.δ i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ≫
        (triangleLeftCancellationCylinder T U v).homotopy.h := by
  rw [triangleLeftCancellationUpperComparison, familyHomotopyEndpointTransport_h]
  change _ = fst (Δ[1] : SSet.{u}) Δ[1] ≫ stdSimplex.δ i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ≫
    ThreeEdgeTransport.square (triangleLeftCancellationTransport T U v)
  rw [ThreeEdgeTransport.square_upper]
  exact hr i

omit hr in
/-- 固定下面の全三辺も、同じ元の辺に全時刻固定する。 -/
lemma triangleLeftCancellationLowerComparison_edge (i : Fin 3) :
    (stdSimplex.δ i ▷ (Δ[1] : SSet.{u})) ≫
        (triangleLeftCancellationLowerComparison T U v w).h =
      fst (Δ[1] : SSet.{u}) Δ[1] ≫ stdSimplex.δ i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫
        (triangleLeftCancellationCylinder T U v).homotopy.h := by
  rw [triangleLeftCancellationLowerComparison, familyHomotopyEndpointTransport_h]
  change (stdSimplex.δ i ▷ (Δ[1] : SSet.{u})) ≫ fst Δ[2] Δ[1] ≫ _ =
    fst (Δ[1] : SSet.{u}) Δ[1] ≫ stdSimplex.δ i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫
      ThreeEdgeTransport.square (triangleLeftCancellationTransport T U v)
  rw [whiskerRight_fst_assoc, ThreeEdgeTransport.square_lower]
  rfl

/-- 全残面比較と固定下面は、同じ全対角比較円柱を共有する。 -/
lemma triangleLeftCancellationComparison_diagonal :
    (stdSimplex.δ 1 ▷ (Δ[1] : SSet.{u})) ≫
        (triangleLeftCancellationUpperComparison T U v w H).h =
      (stdSimplex.δ 1 ▷ (Δ[1] : SSet.{u})) ≫
        (triangleLeftCancellationLowerComparison T U v w).h := by
  rw [triangleLeftCancellationUpperComparison_edge T U v w H hr,
    triangleLeftCancellationLowerComparison_edge]
  simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper_diagonal, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower_diagonal]

/-- 元の全残面比較を保持する、出力した全円柱の実高次比較。 -/
def triangleLeftCancellationCylinderComparisonFromTriangle : SSet.Homotopy
    (triangleLeftCancellationCylinder T U v).homotopy.h
    (triangleLeftCancellationCylinder T U w).homotopy.h :=
  squareTriangleHomotopy (triangleLeftCancellationUpperComparison T U v w H)
    (triangleLeftCancellationLowerComparison T U v w)
    (triangleLeftCancellationComparison_diagonal T U v w H hr)

/-- 出力円柱の入力全境界と元の比較時刻の両端を、全高次比較時刻で同時に固定する。 -/
lemma triangleLeftCancellationCylinderComparisonFromTriangle_relative :
    (fullCylinderBoundaryInclusion (SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫
        (triangleLeftCancellationCylinderComparisonFromTriangle T U v w H hr).h =
      fst (fullCylinderBoundary (SSet.boundary 1).ι) Δ[1] ≫
        fullCylinderBoundaryInclusion (SSet.boundary 1).ι ≫
          (triangleLeftCancellationCylinder T U v).homotopy.h :=
  squareTriangleHomotopy_relative _ _ _
    (triangleLeftCancellationUpperComparison_edge T U v w H hr)
    (triangleLeftCancellationLowerComparison_edge T U v w)

/-- 指定した同じ全残面比較を、出力円柱比較の上面に厳密に保持する。 -/
lemma triangleLeftCancellationCylinderComparisonFromTriangle_upper :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ▷ (Δ[1] : SSet.{u})) ≫
        (triangleLeftCancellationCylinderComparisonFromTriangle T U v w H hr).h = H.h :=
  (squareTriangleHomotopyMap_upper _ _ _).trans (familyHomotopyEndpointTransport_h _ _ _)

/-- 全基底比較の両三角形を指定すれば、出力した全高次円柱も同じ全基底像を保つ。 -/
lemma triangleLeftCancellationCylinderComparisonFromTriangle_projection
    {B : SSet.{u}} (p : E ⟶ B)
    (q : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) ⊗ Δ[1] ⟶ B)
    (hu : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ▷ (Δ[1] : SSet.{u})) ≫ q = H.h ≫ p)
    (hl : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ▷ (Δ[1] : SSet.{u})) ≫ q =
      fst (Δ[2] : SSet.{u}) Δ[1] ≫
        SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.compId b).simplex ≫ p) :
    (triangleLeftCancellationCylinderComparisonFromTriangle T U v w H hr).h ≫ p = q := by
  apply squareTriangleHomotopyMap_projection
  · rw [triangleLeftCancellationUpperComparison, familyHomotopyEndpointTransport_h]
    exact hu
  · rw [triangleLeftCancellationLowerComparison, familyHomotopyEndpointTransport_h]
    exact hl

omit hr
variable [KanComplex E]

/-- 同じ元の三面を持つ消去四面体の二選択から、全出力円柱の実高次比較を得る。 -/
def triangleLeftCancellationCylinderComparison :=
  triangleLeftCancellationCylinderComparisonFromTriangle T U v w
    (triangleLeftCancellationTriangleComparison T U v w)
    (triangleLeftCancellationTriangleComparison_edge T U v w)

/-- 二選択の全出力円柱比較は、両全境界を全高次比較時刻で同時に固定する。 -/
lemma triangleLeftCancellationCylinderComparison_relative :
    (fullCylinderBoundaryInclusion (SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫
        (triangleLeftCancellationCylinderComparison T U v w).h =
      fst (fullCylinderBoundary (SSet.boundary 1).ι) Δ[1] ≫
        fullCylinderBoundaryInclusion (SSet.boundary 1).ι ≫
          (triangleLeftCancellationCylinder T U v).homotopy.h :=
  triangleLeftCancellationCylinderComparisonFromTriangle_relative _ _ _ _ _ _

/-- 元の全消去四面体比較の残面全体を、同じ出力円柱比較の上面に保持する。 -/
lemma triangleLeftCancellationCylinderComparison_upper :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ▷ (Δ[1] : SSet.{u})) ≫
        (triangleLeftCancellationCylinderComparison T U v w).h =
      (triangleLeftCancellationTriangleComparison T U v w).h :=
  triangleLeftCancellationCylinderComparisonFromTriangle_upper _ _ _ _ _ _

end SerrePositivity.KST.SConstruction
