module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointCounitCoordinates
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointStructureIntervals
public import SerrePositivity.KST.Spectra.PointedTransposeIntervalRestriction
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.FreeIntervalBoundary

/-!
概要：元の構造比較区間の counit 像を実際の区間として計算し、始点を元の二段構造へ同定する。
方針：counit の源自然性と元の全 Hom の厳密な段条件を用いる。
規約：二端点の厳密一致や収縮は未主張。使われ方：全列ホモトピーの非定数始点境界の解析。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence)

/-- 元の構造区間の始点の counit 像は、元の二段構造への厳密な制限。 -/
lemma kanAdjointStructureCounit_source (n : ℕ) :
    ((φ ≫ kanAdjointParameterLeft X Y (n + 1)) ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
        (PointedObject.basedHom CirclePower.space (Y.level (n + 2)).space)) ≫
      kanLoopCounit (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.level (n + 2)).space =
    φ ≫ pointedEvaluation X Y.toKanSequence (n + 2) ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed
        (PointedSimplicialSet.circle.{u} ◁ X.sigma n ≫ X.sigma (n + 1))
        (Y.level (n + 2)).space := by
  rw [Category.assoc, kanLoopCounit_pre, ← Category.assoc, Category.assoc φ,
    kanAdjointParameterLeft_counit]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp]

/-- 同じ実構造区間を counit へ写し、元の二段評価を始点に持つ区間として保持する。 -/
def kanAdjointStructureCounitInterval (n : ℕ) :
    PointedMapping.VerticalPath
      (PointedObject.toPoint (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space))
        (Y.level (n + 2)).space))
      (φ ≫ pointedEvaluation X Y.toKanSequence (n + 2) ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed
          (PointedSimplicialSet.circle.{u} ◁ X.sigma n ≫ X.sigma (n + 1))
          (Y.level (n + 2)).space)
      (((φ ≫ kanAdjointParameterLeft X Y n) ≫
        pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n) ≫
        kanLoopCounit (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.level (n + 2)).space) :=
  ((kanAdjointParameterStructureInterval X Y φ n).basedPost
    (kanLoopCounit (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.level (n + 2)).space)).changeEndpoints
      (kanAdjointStructureCounit_source X Y φ n).symm rfl

/-- counit 像も、任意に選び直した区間ではなく元の係数区間の同じ後合成。 -/
lemma kanAdjointStructureCounitInterval_h (n : ℕ) :
    (kanAdjointStructureCounitInterval X Y φ n).homotopy.h =
      (kanAdjointParameterStructureInterval X Y φ n).homotopy.h ≫
        (kanLoopCounit (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.level (n + 2)).space).right := by
  rw [kanAdjointStructureCounitInterval, PointedMapping.VerticalPath.changeEndpoints_homotopy_h,
    PointedMapping.VerticalPath.basedPost_homotopy_h]

/-- 元の指定部分への制限も、同じ係数区間の制限と counit 後合成で厳密に計算される。 -/
lemma kanAdjointStructureCounitInterval_boundary {B : PointedSimplicialSet.{u}}
    (j : B ⟶ A) (n : ℕ) :
    j.right ▷ (Δ[1] : SSet.{u}) ≫ (kanAdjointStructureCounitInterval X Y φ n).homotopy.h =
      (j ≫ kanAdjointStructureInput X Y φ n).right ▷ (Δ[1] : SSet.{u}) ≫
        (kanAdjointCoefficientReversePath X Y n).homotopy.h ≫
        (kanLoopCounit (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.level (n + 2)).space).right := by
  rw [kanAdjointStructureCounitInterval_h, ← Category.assoc,
    kanAdjointParameterStructureInterval_boundary, Category.assoc]

end SerrePositivity.KST.Spectra.RawSpectrumMapping
