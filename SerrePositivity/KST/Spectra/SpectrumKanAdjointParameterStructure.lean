module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointParameterNaturality
public import SerrePositivity.KST.Spectra.PointedCurryingParameterComponents
public import SerrePositivity.KST.Spectra.SignedLoopSequence

/-!
概要：元の全 Hom の評価を Kan 随伴へ後合成した族の、符号付き loop 列の構造成分式。
方針：段比較を同じ懸垂 Hom からの後合成に直し、随伴の構造成分式を内部 Hom へ移す。
規約：全 Hom のパラメータ全体を使用。使われ方：列方向の厳密化への実際の入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 懸垂 Hom の後合成自然性を、元の点つき射として使う。 -/
lemma suspensionHom_post_pointed (A : PointedSimplicialSet.{u})
    {B D : PointedSimplicialSet.{u}} (f : B ⟶ D) :
    (ihom A).map f ≫ suspensionHom A D =
      suspensionHom A B ≫ (ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension A)).map
        (PointedSimplicialSet.circle.{u} ◁ f) := by
  apply Under.UnderMorphism.ext
  exact SerrePositivity.InfinityCategories.HomotopyLimits.suspensionHom_post A f

/-- 標的の随伴を含む段比較を、元の懸垂 Hom からの後合成として厳密に計算する。 -/
lemma kanAdjointParameterLeft_step (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    kanAdjointParameterLeft X Y n ≫
    pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n =
    (pointedEvaluation X Y.toKanSequence n ≫
      suspensionHom (X.level n).space (Y.level n).space) ≫
    (ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)).map
      (PointedSimplicialSet.circle.{u} ◁ KanSequence.kanAdjoint Y.toKanSequence n ≫
        (KanSequence.signedLoopTail Y.toKanSequence).sigma n) := by
  change (pointedEvaluation X Y.toKanSequence n ≫
    (ihom (X.level n).space).map _) ≫ (suspensionHom _ _ ≫
      (ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)).map _) = _
  rw [Functor.map_comp]
  have he := congrArg
    (fun p ↦ pointedEvaluation X Y.toKanSequence n ≫ p ≫
      (ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)).map
        ((KanSequence.signedLoopTail Y.toKanSequence).sigma n))
    (suspensionHom_post_pointed (X.level n).space
      (KanSequence.kanAdjoint Y.toKanSequence n))
  simp only [Category.assoc] at he ⊢
  exact he

/-- 源の構造射への制限も、同じ懸垂 Hom からの後合成として厳密に計算する。 -/
lemma kanAdjointParameterLeft_source_restriction (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    kanAdjointParameterLeft X Y (n + 1) ≫
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
      ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space =
    (pointedEvaluation X Y.toKanSequence n ≫
      suspensionHom (X.level n).space (Y.level n).space) ≫
    (ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)).map
      (Y.sigma n ≫ KanSequence.kanAdjoint Y.toKanSequence (n + 1)) := by
  have he := (pre (X.sigma n)).naturality
    (KanSequence.kanAdjoint Y.toKanSequence (n + 1))
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at he
  have he' := congrArg (pointedEvaluation X Y.toKanSequence (n + 1) ≫ ·) he
  have he'' : kanAdjointParameterLeft X Y (n + 1) ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
        ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space =
      (pointedEvaluation X Y.toKanSequence (n + 1) ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n) (Y.level (n + 1)).space) ≫
        (ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)).map
          (KanSequence.kanAdjoint Y.toKanSequence (n + 1)) := by
    simp only [kanAdjointParameterLeft, Category.assoc]
    exact he'
  have hc : pointedEvaluation X Y.toKanSequence (n + 1) ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n) (Y.level (n + 1)).space =
      pointedEvaluation X Y.toKanSequence n ≫ pointedStep X Y.toKanSequence n :=
    pointedEvaluation_condition X Y.toKanSequence n
  rw [he'', hc]
  change (pointedEvaluation X Y.toKanSequence n ≫
    (suspensionHom _ _ ≫ (ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)).map _)) ≫ _ = _
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rfl

/-- 全 Hom の標的の Kan 随伴への後合成は、符号付き loop 列の段条件を成分で満たす。 -/
lemma kanAdjointParameterLeft_condition (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    PointedMapping.componentOf (kanAdjointParameterLeft X Y n ≫
      pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n) =
    PointedMapping.componentOf (kanAdjointParameterLeft X Y (n + 1) ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
        ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space) := by
  have h := PointedMapping.componentOf_comp_left
    (PointedMapping.componentOf_ihom_map (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
      (KanSequence.kanAdjoint_signedLoopTail_comm Y.toKanSequence_omega n))
    (pointedEvaluation X Y.toKanSequence n ≫
      suspensionHom (X.level n).space (Y.level n).space)
  rw [kanAdjointParameterLeft_step, kanAdjointParameterLeft_source_restriction]
  exact h

end SerrePositivity.KST.Spectra.RawSpectrumMapping
