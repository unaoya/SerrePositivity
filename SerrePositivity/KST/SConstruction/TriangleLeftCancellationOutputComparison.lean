module
public import SerrePositivity.KST.SConstruction.TriangleLeftCancellationCylinderComparison

/-! # 指定された消去四面体全体の比較から全出力比較を回収する
概要：同じ三面を固定する任意の全四面体比較を、全残面・全出力円柱の比較へ戻す。
方針：零面をそのまま取り、各境界辺を元の固定三面へ因子分解する。
規約：元の全四面体比較を指定面に保持し、新しい比較四面体を選ばない。
使われ方：fibration に沿って持ち上げた元の全基底比較を出力円柱まで保持する。
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
  (H : SSet.Homotopy (triangleLeftCancellationAt T U v) (triangleLeftCancellationAt T U w))
  (hr : ((horn 3 (0 : Fin 4)).ι ▷ (Δ[1] : SSet.{u})) ≫ H.h =
    fst (Λ[3, 0] : SSet.{u}) Δ[1] ≫ triangleLeftCancellationHorn T U)

/-- 指定した元の全四面体比較の零面を、そのまま元の両残面の比較として回収する。 -/
def triangleLeftCancellationOutputTriangleComparison :=
  familyHomotopyEndpointTransport (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H (stdSimplex.δ 0))
    (triangleLeftCancellationTriangle_face T U v)
    (triangleLeftCancellationTriangle_face T U w).symm

/-- 同じ全残面比較は、指定した元の全四面体比較の零面そのもの。 -/
lemma triangleLeftCancellationOutputTriangleComparison_h :
    (triangleLeftCancellationOutputTriangleComparison T U v w H).h =
      (stdSimplex.δ 0 ▷ (Δ[1] : SSet.{u})) ≫ H.h :=
  familyHomotopyEndpointTransport_h _ _ _

include hr

/-- 元の全指定三面を全比較時刻で厳密に保持する。 -/
lemma triangleLeftCancellationOutputComparison_face (j : Fin 4) (hj : j ≠ 0) :
    (stdSimplex.δ j ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst (Δ[2] : SSet.{u}) Δ[1] ≫ triangleLeftCancellationFaces T U j hj := by
  rw [← horn.ι_ι (0 : Fin 4) j hj, comp_whiskerRight, Category.assoc, hr,
    whiskerRight_fst_assoc, triangleLeftCancellationHorn_face]

/-- 残面の全三辺を元の固定三面に沿って全比較時刻で厳密に固定する。 -/
lemma triangleLeftCancellationOutputTriangleComparison_edge (i : Fin 3) :
    (stdSimplex.δ i ▷ (Δ[1] : SSet.{u})) ≫
        (triangleLeftCancellationOutputTriangleComparison T U v w H).h =
      fst (Δ[1] : SSet.{u}) Δ[1] ≫ stdSimplex.δ i ≫
        SSet.yonedaEquiv.symm (triangleLeftCancellationTriangle T U v).simplex := by
  have he : stdSimplex.δ.{u} i ≫ stdSimplex.δ (0 : Fin 4) =
      stdSimplex.δ (0 : Fin 3) ≫ stdSimplex.δ i.succ := by
    apply SSet.yonedaEquiv.injective
    apply SSet.stdSimplex.ext
    intro k
    fin_cases i <;> fin_cases k <;> rfl
  rw [triangleLeftCancellationOutputTriangleComparison_h, ← Category.assoc,
    ← comp_whiskerRight, he, comp_whiskerRight, Category.assoc,
    triangleLeftCancellationOutputComparison_face T U v w H hr i.succ (Fin.succ_ne_zero i),
    whiskerRight_fst_assoc, triangleLeftCancellationTriangle_face]
  rw [← Category.assoc (stdSimplex.δ i), he, Category.assoc,
    triangleLeftCancellationAt_face T U v i.succ (Fin.succ_ne_zero i)]

/-- 指定した元の全四面体比較からの、同じ全出力円柱の実高次比較。 -/
def triangleLeftCancellationOutputComparison :=
  triangleLeftCancellationCylinderComparisonFromTriangle T U v w
    (triangleLeftCancellationOutputTriangleComparison T U v w H)
    (triangleLeftCancellationOutputTriangleComparison_edge T U v w H hr)

/-- 出力円柱の入力全境界と比較時刻の両端を、全高次比較時刻で同時に固定する。 -/
lemma triangleLeftCancellationOutputComparison_relative :
    (fullCylinderBoundaryInclusion (SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫
        (triangleLeftCancellationOutputComparison T U v w H hr).h =
      fst (fullCylinderBoundary (SSet.boundary 1).ι) Δ[1] ≫
        fullCylinderBoundaryInclusion (SSet.boundary 1).ι ≫
          (triangleLeftCancellationCylinder T U v).homotopy.h :=
  triangleLeftCancellationCylinderComparisonFromTriangle_relative _ _ _ _ _ _

/-- 指定した元の全四面体比較の零面を、同じ全出力円柱比較の上面に保持する。 -/
lemma triangleLeftCancellationOutputComparison_upper :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ▷ (Δ[1] : SSet.{u})) ≫
        (triangleLeftCancellationOutputComparison T U v w H hr).h =
      (stdSimplex.δ 0 ▷ (Δ[1] : SSet.{u})) ≫ H.h :=
  (triangleLeftCancellationCylinderComparisonFromTriangle_upper _ _ _ _ _ _).trans
    (triangleLeftCancellationOutputTriangleComparison_h T U v w H)

end SerrePositivity.KST.SConstruction
