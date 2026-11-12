module
public import SerrePositivity.KST.SConstruction.TracedTripleGeometricPrefixComparison
public import SerrePositivity.KST.SConstruction.TriangleLeftCancellationCylinderComparisonOver

/-! # 元の構造射制限に沿い最後の消去の全基底比較を保持する
概要：元の単射源構造射による Hom 制限に沿い、指定全四面体比較を全出力比較へ戻す。
方針：同じ制限の fibration 性を使い、元の指定三面と全基底比較を同時に保持する。
規約：全基底比較と三面固定式は明示的な入力。隣接段適合全体の完成とは数えない。
使われ方：六結合替えと全三辺移送の高次 prism が到着した後の、最後の消去。
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
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})

/-- 元の単射源構造射による、次段全写像空間の同じ制限。 -/
def monicKTracedTripleStageRestriction (w z : I) (n : ℕ) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj w)).sigma n)
    ((kKanSequence (F.obj z)).level (n + 1)).space

/-- 元の同じ次段制限は、追加のモデル圏仮定なしで fibration。 -/
instance monicKTracedTripleStageRestriction_fibration (w z : I) (n : ℕ) :
    Fibration (monicKTracedTripleStageRestriction F w z n) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_fibration ((kOmegaSpectrum (F.obj w)).sigma n)
    ((kKanSequence (F.obj z)).level (n + 1)).space

variable {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z) (n : ℕ)
  (v : (triangleLeftCancellationChoices
    (monicKTracedTripleGeometricStagePasting F f g h (n + 1)).transported
    (monicKTracedTripleGeometricStagePasting F f g h (n + 1)).bottom.triangle) _⦋0⦌)
  (H : SSet.Homotopy
    (triangleLeftCancellationAt
      (monicKTracedTripleGeometricStagePasting F f g h (n + 1)).transported
      (monicKTracedTripleGeometricStagePasting F f g h (n + 1)).bottom.triangle
      (monicKTracedTripleGeometricStagePasting F f g h (n + 1)).prefixChoice ≫
        monicKTracedTripleStageRestriction F w z n)
    (triangleLeftCancellationAt
      (monicKTracedTripleGeometricStagePasting F f g h (n + 1)).transported
      (monicKTracedTripleGeometricStagePasting F f g h (n + 1)).bottom.triangle v ≫
        monicKTracedTripleStageRestriction F w z n))
  (hr : ((horn 3 (0 : Fin 4)).ι ▷ (Δ[1] : SSet.{u})) ≫ H.h =
    fst (Λ[3, 0] : SSet.{u}) Δ[1] ≫ triangleLeftCancellationHorn
      (monicKTracedTripleGeometricStagePasting F f g h (n + 1)).transported
      (monicKTracedTripleGeometricStagePasting F f g h (n + 1)).bottom.triangle ≫
        monicKTracedTripleStageRestriction F w z n)

/-- 元の次段制限に沿い、指定全基底比較を保って最後の消去の全出力を比較する。 -/
def monicKTracedTripleGeometricPrefixStructureComparison :=
  triangleLeftCancellationCylinderComparisonOver
    (monicKTracedTripleGeometricStagePasting F f g h (n + 1)).transported
    (monicKTracedTripleGeometricStagePasting F f g h (n + 1)).bottom.triangle
    (monicKTracedTripleGeometricStagePasting F f g h (n + 1)).prefixChoice v
    (monicKTracedTripleStageRestriction F w z n) H hr

/-- 同じ実持ち上げは、入力全境界と元の比較時刻の両端を全高次比較時刻で固定する。 -/
lemma monicKTracedTripleGeometricPrefixStructureComparison_relative :
    (fullCylinderBoundaryInclusion (SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedTripleGeometricPrefixStructureComparison F f g h n v H hr).h =
      fst (fullCylinderBoundary (SSet.boundary 1).ι) Δ[1] ≫
        fullCylinderBoundaryInclusion (SSet.boundary 1).ι ≫
          (monicKTracedTripleGeometricRawStageComparison F f g h (n + 1)).homotopy.h :=
  (triangleLeftCancellationCylinderComparisonOver_relative
    (monicKTracedTripleGeometricStagePasting F f g h (n + 1)).transported
    (monicKTracedTripleGeometricStagePasting F f g h (n + 1)).bottom.triangle
    (monicKTracedTripleGeometricStagePasting F f g h (n + 1)).prefixChoice v
    (monicKTracedTripleStageRestriction F w z n) H hr).trans
      (congrArg (fun q => fst (fullCylinderBoundary (SSet.boundary 1).ι) Δ[1] ≫
        fullCylinderBoundaryInclusion (SSet.boundary 1).ι ≫ q)
        (monicKTracedTripleGeometricRawStageComparison_h F f g h (n + 1)).symm)

/-- 全出力比較の上面の構造射制限は、元の指定全基底比較の零面そのもの。 -/
lemma monicKTracedTripleGeometricPrefixStructureComparison_upper_projection :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedTripleGeometricPrefixStructureComparison F f g h n v H hr).h ≫
          monicKTracedTripleStageRestriction F w z n =
      (stdSimplex.δ 0 ▷ (Δ[1] : SSet.{u})) ≫ H.h :=
  triangleLeftCancellationCylinderComparisonOver_upper_projection _ _ _ _ _ _ _

/-- 指定全基底円柱の両全面を保持すれば、次段の全出力比較も同じ全基底像を保つ。 -/
lemma monicKTracedTripleGeometricPrefixStructureComparison_projection
    (q : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) ⊗ Δ[1] ⟶
      (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kOmegaSpectrum (F.obj w)).level n).space)
        ((kKanSequence (F.obj z)).level (n + 1)).space).right)
    (hu : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ▷ (Δ[1] : SSet.{u})) ≫ q =
      (stdSimplex.δ 0 ▷ (Δ[1] : SSet.{u})) ≫ H.h)
    (hl : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ▷ (Δ[1] : SSet.{u})) ≫ q =
      fst (Δ[2] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm
        (SSet.Edge.CompStruct.compId
          (monicKTracedTripleLeftStageEdgeData F f g h (n + 1)).second).simplex ≫
            monicKTracedTripleStageRestriction F w z n) :
    (monicKTracedTripleGeometricPrefixStructureComparison F f g h n v H hr).h ≫
        monicKTracedTripleStageRestriction F w z n = q :=
  triangleLeftCancellationCylinderComparisonOver_projection _ _ _ _ _ _ _ q hu hl

end SerrePositivity.KST.SConstruction
