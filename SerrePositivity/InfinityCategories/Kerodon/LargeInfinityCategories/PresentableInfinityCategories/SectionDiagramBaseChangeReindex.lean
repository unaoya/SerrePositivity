module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.TransposeFunctorIsoComposition

/-!
概要：転置後の指定相対切断底変換同型と添字制限の全自然な両立。
方針：既存定義の転置を正規化し、元の実現同型の添字制限を移す。
規約：指定された底変換同型そのものを比較する。
使われ方：P-12 の単体切断底変換の合成への接続。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：元の転置後の切断底変換同型を端点正規化した転置として回収する。
方針：既存定義の端点書き換えを異種等式で除く。
規約：元の実現同型を使う。使われ方：添字制限と合成の転置の正規化。 -/
lemma relativeSectionDiagramInfinityBaseChangeIso_normalized {B D : SSet.{u}}
    {J : Type u} [Category.{u} J] (k : D ⟶ B) (A : Jᵒᵖ ⥤ Over D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeSectionDiagramInfinityBaseChangeIso k A =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.diagramIsoCongr
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transposeFunctorFamily_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibrationInfinityBaseChange k)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram A).realization) rfl
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionBaseChangeRealizationIso k A).transpose := by
  have he : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeSectionDiagramInfinityBaseChangeIso k A)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionBaseChangeRealizationIso k A).transpose := by
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeSectionDiagramInfinityBaseChangeIso
    dsimp only [_root_.id]
    have hcast {T U : Sort (u + 2)} (h : T = U) (z : T) : HEq (Eq.mp h z) z := by
      cases h
      rfl
    exact hcast _ _
  exact eq_of_heq (he.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.diagramIsoCongr_heq _ _ _).symm)

/-- 概要：元の相対切断底変換同型は添字関手の制限と全自然に両立する。
方針：元の実現同型の制限の式を転置し端点を同じ切断図式に揃える。
規約：対象ごとの比較ではなく図式全体の指定同型の等式。
使われ方：全単体の添字制限を使った指定 straightening 合成の降下。 -/
lemma relativeSectionDiagramInfinityBaseChangeIso_reindex {B D : SSet.{u}}
    {J L : Type u} [Category.{u} J] [Category.{u} L]
    (k : D ⟶ B) (A : Jᵒᵖ ⥤ Over D) (H : L ⥤ J) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeSectionDiagramInfinityBaseChangeIso k (H.op ⋙ A) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.diagramIsoCongr
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun f ↦ f ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibrationInfinityBaseChange k)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
            (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionDiagramInfinity_reindex A H)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionDiagramInfinity_reindex (A ⋙ Over.map k) H)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeSectionDiagramInfinityBaseChangeIso k A).precomp
          ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap H))) := by
  rw [relativeSectionDiagramInfinityBaseChangeIso_normalized,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.relativeSectionBaseChangeRealizationIso_reindex,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.diagramIsoCongr_transpose, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.diagramIsoCongr_comp]
  let q := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap H)
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionBaseChangeRealizationIso k A
  let hf := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.transposeFunctorFamily_pre
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibrationInfinityBaseChange k ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram A).realization) q
  let hg := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.transposeFunctorFamily_pre
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram (A ⋙ Over.map k)).realization q
  have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorIsoTranspose_postcomp_pre q e
  rw [relativeSectionDiagramInfinityBaseChangeIso_normalized k A,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.diagramIsoCongr_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.diagramIsoCongr_comp]
  rw [← hr, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.diagramIsoCongr_comp]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
