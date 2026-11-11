module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaYonedaFiniteCoproducts
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LimitColimitOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitDiagramIso

/-!
概要：元の底の有限余積と、その P_Σ Yoneda 像の余積の存在。
方針：反対圏の有限積を元の全余錐へ戻し、構成済みの保存定理を適用する。
規約：元の底の有限積仮定をそのまま公開入力に保つ。
使われ方：表現可能前層の小余積を有限部分集合の filtered 余極限で構成する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：元の反対圏の有限積から元の底の全有限余積が存在する。
方針：離散形状の反転同型と同じ図式の双対極限を使う。
規約：空添字を含む元の有限図式を保持する。
使われ方：P_Σ Yoneda の有限余積表示の存在入力。 -/
lemma hasFiniteCoproducts_of_op_finiteProducts {C : SSet.{u}} [Quasicategory C]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p)
    {J : Type u} [Finite J] (p : nerve (Discrete J) ⟶ C) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanHasColimit_iff_hasLimit_op p).mpr
  let e := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.discreteNerveOppositeIso J
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasLimit_iff_restrict_of_precompositionEquivalence (SSet.opFunctor.map p) e.inv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso e.symm)).mpr (hC J (e.inv ≫ SSet.opFunctor.map p))

/-- 概要：元の底の有限余積図式の Yoneda 像は P_Σ 内で同じ余積を持つ。
方針：元の指定余錐の存在と有限余積保存を合わせる。
規約：空添字と全ての元の脚を保持する。
使われ方：表現可能前層の小余積の有限段。 -/
lemma sigmaYoneda_finiteDiagram_hasColimit {C : SSet.{u}} [Quasicategory C]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p)
    {J : Type u} [Finite J] (p : nerve (Discrete J) ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit ((SSet.uliftFunctor.{u + 1, u}).map p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C) := by
  obtain ⟨c, hc⟩ := hasFiniteCoproducts_of_op_finiteProducts hC p
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift.{u, u + 1} c),
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYoneda_finiteCoproduct_isColimit c hc⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
