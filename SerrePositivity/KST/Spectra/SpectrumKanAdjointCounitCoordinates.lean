module

public import SerrePositivity.KST.Spectra.KanLoopCounitCoordinates

/-!
概要：元の Kan 随伴の二つの全パラメータ座標を、通常の円の counit で厳密に評価する。
方針：元の制限式と段の厳密可換式をテンソル内部 Hom 同型で戻す。
規約：自然性区間と構造比較区間を混同しない。使われ方：全列比較の端点と残境界の計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u})

/-- 標的の Kan 随伴の counit 像は、元の次段評価の構造射への制限そのもの。 -/
lemma kanAdjointParameterLeft_counit (n : ℕ) :
    kanAdjointParameterLeft X Y n ≫ kanLoopCounit (X.level n).space (Y.level (n + 1)).space =
      pointedEvaluation X Y.toKanSequence (n + 1) ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n) (Y.level (n + 1)).space := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso PointedSimplicialSet.circle
    (X.level n).space (Y.level (n + 1)).space).hom).1
  rw [Category.assoc, kanLoopCounit_comparison]
  change kanAdjointParameterLeft X Y n ≫ kanAdjointParameterRestriction X Y n = _
  exact (kanAdjointParameterLeft_restriction X Y n).trans
    (pointedEvaluation_adjoint_condition X Y n).symm

/-- 源の Kan 随伴の counit 像も、同じ次段評価の構造射への制限へ厳密に一致する。 -/
lemma kanAdjointParameterRight_counit (n : ℕ) :
    kanAdjointParameterRight X Y n ≫ kanLoopCounit (X.level n).space (Y.level (n + 1)).space =
      pointedEvaluation X Y.toKanSequence (n + 1) ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n) (Y.level (n + 1)).space := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso PointedSimplicialSet.circle
    (X.level n).space (Y.level (n + 1)).space).hom).1
  rw [Category.assoc, kanLoopCounit_comparison]
  change kanAdjointParameterRight X Y n ≫ kanAdjointParameterRestriction X Y n = _
  exact (kanAdjointParameterRight_restriction X Y n).trans
    (pointedEvaluation_adjoint_condition X Y n).symm

/-- 元の自然性ホモトピーは、counit の後では同じ元の厳密な段条件で全区間が一定。 -/
lemma kanAdjointParameterHomotopy_counit (n : ℕ) :
    (kanAdjointParameterHomotopy X Y n).h ≫
        (kanLoopCounit (X.level n).space (Y.level (n + 1)).space).right =
      fst (pointedSpace X Y.toKanSequence).right (Δ[1] : SSet.{u}) ≫
        (pointedEvaluation X Y.toKanSequence (n + 1) ≫
          _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n) (Y.level (n + 1)).space).right := by
  have hc := congrArg Under.Hom.right (kanAdjointParameterLeft_counit X Y n)
  change (kanAdjointParameterLeft X Y n).right ≫
    (kanLoopCounit (X.level n).space (Y.level (n + 1)).space).right = _ at hc
  have hf : (kanAdjointParameterRestriction X Y n).right ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso PointedSimplicialSet.circle.{u}
        (X.level n).space (Y.level (n + 1)).space).inv.right =
      (kanLoopCounit (X.level n).space (Y.level (n + 1)).space).right := rfl
  have h := congrArg (· ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso PointedSimplicialSet.circle.{u}
    (X.level n).space (Y.level (n + 1)).space).inv.right)
    (kanAdjointParameterHomotopy_restriction X Y n)
  simp only [Category.assoc, hf] at h
  exact h.trans (congrArg (fst (pointedSpace X Y.toKanSequence).right (Δ[1] : SSet.{u}) ≫ ·) hc)

end SerrePositivity.KST.Spectra.RawSpectrumMapping
