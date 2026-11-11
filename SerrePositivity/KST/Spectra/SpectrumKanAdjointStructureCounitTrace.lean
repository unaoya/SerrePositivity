module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointStructureCounit
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointTracedRectification

/-!
概要：合成正方形の元の非定数構造区間を再び転置し、同じ counit 像の実区間へ照合する。
方針：保存済みの区間族の式と二度の転置の往復則を使い、選び直しを排除する。
規約：像の収縮は未主張。使われ方：元の始点境界の評価による移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence)

/-- 同じ元の構造区間を再び転置すると、元の段座標の実区間そのものへ戻る。 -/
lemma kanAdjointTracedStructureInterval_transpose_path (n : ℕ) :
    (kanAdjointTracedStructureInterval X Y φ n).basedTranspose.path =
      (kanAdjointParameterStructureInterval X Y φ n).path := by
  have he := congrArg (· ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) A
    ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space).hom.right)
    (kanAdjointTracedStructureInterval_path X Y φ n)
  change (kanAdjointTracedStructureInterval X Y φ n).basedTranspose.path =
    (kanAdjointParameterStructureInterval X Y φ n).basedTranspose.basedTranspose.path at he
  exact he.trans (kanAdjointParameterStructureInterval X Y φ n).basedTranspose_twice_path

/-- 元の合成正方形の構造区間を、同じ counit で評価した実区間。 -/
def kanAdjointTracedStructureCounitInterval (n : ℕ) :=
  (kanAdjointTracedStructureInterval X Y φ n).basedTranspose.basedPost
    (kanLoopCounit (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.level (n + 2)).space)

/-- 転置後の counit 像は、元の段座標で計算した同じ実区間の族そのもの。 -/
lemma kanAdjointTracedStructureCounitInterval_path (n : ℕ) :
    (kanAdjointTracedStructureCounitInterval X Y φ n).path =
      (kanAdjointStructureCounitInterval X Y φ n).path := by
  let P := (kanAdjointParameterStructureInterval X Y φ n).basedPost
    (kanLoopCounit (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.level (n + 2)).space)
  have he := congrArg (· ≫ (PointedObject.basedHomMap A
    (kanLoopCounit (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.level (n + 2)).space)).right)
    (kanAdjointTracedStructureInterval_transpose_path X Y φ n)
  change (kanAdjointTracedStructureCounitInterval X Y φ n).path = P.path at he
  have hq := PointedMapping.VerticalPath.path_eq_of_homotopy_h_eq
    (kanAdjointStructureCounitInterval X Y φ n) P
    (PointedMapping.VerticalPath.changeEndpoints_homotopy_h P
      (kanAdjointStructureCounit_source X Y φ n).symm rfl)
  exact he.trans hq.symm

end SerrePositivity.KST.Spectra.RawSpectrumMapping
