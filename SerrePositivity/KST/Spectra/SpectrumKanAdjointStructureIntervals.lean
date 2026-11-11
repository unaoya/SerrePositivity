module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointBoundaryCoordinates
public import SerrePositivity.KST.Spectra.PointedBasedIntervalTraces

/-!
概要：元の普遍係数区間と非零境界の段調整区間を、構造比較の同じ Hom へ移す。
方針：元の入力への前合成と後合成だけを使い、部分対象での区間全体を計算する。
規約：区間を成分から選び直さない。使われ方：三辺輸送による構造比較の境界トレース。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 元の構造比較の係数区間へ入力する、元の懸垂評価族。 -/
def kanAdjointStructureInput (X Y : OmegaSpectrum.{u}) {A : PointedSimplicialSet.{u}}
    (φ : A ⟶ pointedSpace X Y.toKanSequence) (n : ℕ) :=
  φ ≫ (pointedEvaluation X Y.toKanSequence n ≫
    suspensionHom (X.level n).space (Y.level n).space)

/-- 元の普遍係数区間を同じ入力へ前合成した、構造比較の実際の区間。 -/
def kanAdjointParameterStructureInterval (X Y : OmegaSpectrum.{u})
    {A : PointedSimplicialSet.{u}} (φ : A ⟶ pointedSpace X Y.toKanSequence) (n : ℕ) :
    PointedMapping.VerticalPath (PointedObject.toPoint
      (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space))
      ((φ ≫ kanAdjointParameterLeft X Y (n + 1)) ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
          ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space)
      ((φ ≫ kanAdjointParameterLeft X Y n) ≫
        pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n) := by
  have hr : ((φ ≫ kanAdjointParameterLeft X Y (n + 1)) ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
        ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space) =
      kanAdjointStructureInput X Y φ n ≫ (ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)).map
        (Y.sigma n ≫ KanSequence.kanAdjoint Y.toKanSequence (n + 1)) := by
    have h := congrArg (φ ≫ ·) (kanAdjointParameterLeft_source_restriction X Y n)
    simp only [kanAdjointStructureInput, Category.assoc] at h ⊢
    exact h
  have hl : ((φ ≫ kanAdjointParameterLeft X Y n) ≫
      pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n) =
      kanAdjointStructureInput X Y φ n ≫ (ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)).map
        (PointedSimplicialSet.circle.{u} ◁ KanSequence.kanAdjoint Y.toKanSequence n ≫
          (KanSequence.signedLoopTail Y.toKanSequence).sigma n) := by
    have h := congrArg (φ ≫ ·) (kanAdjointParameterLeft_step X Y n)
    simp only [kanAdjointStructureInput, Category.assoc] at h ⊢
    exact h
  exact ((kanAdjointCoefficientReversePath X Y n).pre
    (kanAdjointStructureInput X Y φ n)).changeEndpoints hr hl

/-- 構造比較の区間族は、元の普遍係数区間を前合成した族そのもの。 -/
lemma kanAdjointParameterStructureInterval_path (X Y : OmegaSpectrum.{u})
    {A : PointedSimplicialSet.{u}} (φ : A ⟶ pointedSpace X Y.toKanSequence) (n : ℕ) :
    (kanAdjointParameterStructureInterval X Y φ n).path =
      ((kanAdjointCoefficientReversePath X Y n).pre
        (kanAdjointStructureInput X Y φ n)).path := rfl

/-- 構造比較の全区間は、選択済みの同じ普遍係数区間の前合成。 -/
lemma kanAdjointParameterStructureInterval_h (X Y : OmegaSpectrum.{u})
    {A : PointedSimplicialSet.{u}} (φ : A ⟶ pointedSpace X Y.toKanSequence) (n : ℕ) :
    (kanAdjointParameterStructureInterval X Y φ n).homotopy.h =
      (kanAdjointStructureInput X Y φ n).right ▷ (Δ[1] : SSet.{u}) ≫
        (kanAdjointCoefficientReversePath X Y n).homotopy.h := by
  rw [PointedMapping.VerticalPath.homotopy_h, kanAdjointParameterStructureInterval_path,
    ← PointedMapping.VerticalPath.homotopy_h]
  exact PointedMapping.VerticalPath.pre_homotopy_h
    (kanAdjointCoefficientReversePath X Y n) (kanAdjointStructureInput X Y φ n)

/-- 非零境界でも、構造比較のトレースは同じ係数区間への境界入力。 -/
lemma kanAdjointParameterStructureInterval_boundary (X Y : OmegaSpectrum.{u})
    {A B : PointedSimplicialSet.{u}} (φ : A ⟶ pointedSpace X Y.toKanSequence)
    (j : B ⟶ A) (n : ℕ) :
    j.right ▷ (Δ[1] : SSet.{u}) ≫
        (kanAdjointParameterStructureInterval X Y φ n).homotopy.h =
      (j ≫ kanAdjointStructureInput X Y φ n).right ▷ (Δ[1] : SSet.{u}) ≫
        (kanAdjointCoefficientReversePath X Y n).homotopy.h := by
  rw [kanAdjointParameterStructureInterval_h, ← comp_whiskerRight_assoc]
  rfl

namespace KanAdjointBoundaryCoordinate
variable {X Y : OmegaSpectrum.{u}} {A B : PointedSimplicialSet.{u}}
  {φ : A ⟶ pointedSpace X Y.toKanSequence} {j : B ⟶ A}
  {c : B ⟶ pointedSpace X (KanSequence.signedLoopTail Y.toKanSequence)}
  {n : ℕ} {H : KanAdjointBoundaryHomotopy X Y φ j c n}

/-- 保存した段調整ホモトピーそのものを内部 Hom の区間へ移す。 -/
def interval (s : KanAdjointBoundaryCoordinate X Y φ j c n H) :
    PointedMapping.VerticalPath (PointedObject.toPoint (kanAdjointParameterTarget X Y n))
      (φ ≫ kanAdjointParameterLeft X Y n) s.coordinate :=
  PointedMapping.VerticalPath.ofHomotopy s.comparison s.comparison_base (toUnit_unique _ _)

/-- 段調整区間を評価しても、保存した同じ比較ホモトピーに戻る。 -/
lemma interval_h (s : KanAdjointBoundaryCoordinate X Y φ j c n H) :
    s.interval.homotopy.h = s.comparison.h := by
  rw [PointedMapping.VerticalPath.homotopy_h]
  change uncurry (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry A (kanAdjointParameterTarget X Y n)
    s.comparison.h s.comparison_base ≫ _) = _
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι, uncurry_curry]

/-- 段調整を構造 Hom へ後合成した区間の境界は、指定された元の H の同じ後合成。 -/
lemma interval_post_boundary (s : KanAdjointBoundaryCoordinate X Y φ j c n H)
    {E : PointedSimplicialSet.{u}} (k : kanAdjointParameterTarget X Y n ⟶ E) :
    j.right ▷ (Δ[1] : SSet.{u}) ≫ (s.interval.basedPost k).homotopy.h = H.h ≫ k.right := by
  rw [PointedMapping.VerticalPath.basedPost_homotopy_h, interval_h,
    ← Category.assoc, s.comparison_boundary]

end KanAdjointBoundaryCoordinate
end SerrePositivity.KST.Spectra.RawSpectrumMapping
