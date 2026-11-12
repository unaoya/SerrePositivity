module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointCounitCoordinates
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointTracedEvaluationComposite

/-!
概要：選択済みの同じ段合成区間を counit で評価し、元の次段評価の構造制限を始点に持たせる。
方針：元の実区間への後合成と厳密な counit 座標式だけを使う。
規約：全列のホモトピーは未主張。使われ方：元の Hom の段条件に沿う全列比較の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A B : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence) (j : B ⟶ A) [Mono j.right]

/-- 同じ段合成区間の counit 像は、元の厳密な次段評価の構造制限から始まる。 -/
def kanAdjointRelativeTracedCounitInterval (n : ℕ) :
    PointedMapping.VerticalPath
      (PointedObject.toPoint (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        (Y.level (n + 1)).space))
      (φ ≫ pointedEvaluation X Y.toKanSequence (n + 1) ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n) (Y.level (n + 1)).space)
      ((kanAdjointRelativeTracedComparison X Y φ j ≫
        pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n) ≫
        kanLoopCounit (X.level n).space (Y.level (n + 1)).space) := by
  have hs : (φ ≫ kanAdjointParameterLeft X Y n) ≫
      kanLoopCounit (X.level n).space (Y.level (n + 1)).space =
        φ ≫ pointedEvaluation X Y.toKanSequence (n + 1) ≫
          _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n) (Y.level (n + 1)).space := by
    rw [Category.assoc, kanAdjointParameterLeft_counit]
  exact ((kanAdjointRelativeTracedEvaluationInterval X Y φ j n).basedPost
    (kanLoopCounit (X.level n).space (Y.level (n + 1)).space)).changeEndpoints hs.symm rfl

/-- 非零境界への同じ制限は、元の指定境界区間への counit 後合成そのもの。 -/
lemma kanAdjointRelativeTracedCounitInterval_boundary (n : ℕ) :
    j.right ▷ (Δ[1] : SSet.{u}) ≫
        (kanAdjointRelativeTracedCounitInterval X Y φ j n).homotopy.h =
      (kanAdjointTracedBoundaryHomotopy X Y φ j n).h ≫
        (kanLoopCounit (X.level n).space (Y.level (n + 1)).space).right := by
  rw [kanAdjointRelativeTracedCounitInterval,
    PointedMapping.VerticalPath.changeEndpoints_homotopy_h,
    PointedMapping.VerticalPath.basedPost_homotopy_h, ← Category.assoc,
    kanAdjointRelativeTracedEvaluationInterval_boundary]

/-- counit で評価した同じ段区間も、元の全パラメータの基点を全区間で固定する。 -/
lemma kanAdjointRelativeTracedCounitInterval_base (n : ℕ) :
    A.hom ▷ (Δ[1] : SSet.{u}) ≫
        (kanAdjointRelativeTracedCounitInterval X Y φ j n).homotopy.h =
      toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫
        (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.level (n + 1)).space).hom :=
  (kanAdjointRelativeTracedCounitInterval X Y φ j n).homotopy_base

end SerrePositivity.KST.Spectra.RawSpectrumMapping
