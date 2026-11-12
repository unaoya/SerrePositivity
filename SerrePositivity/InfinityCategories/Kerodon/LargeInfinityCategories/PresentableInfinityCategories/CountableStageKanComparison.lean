module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CountableStageComma
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.OppositeSimplexRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ElementsCoproductLeftKan
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.FiniteUniverse

/-!
概要：可算段階関手の局所左 Kan 図式を有限段階の図式へ比較する。
方針：コンマ圏の同値、nerve の左 Kan 比較、宇宙比較を順に合成する。
規約：元の射影と元の有限段階の包含に厳密に可換とする。
使われ方：全有限図式の保存余極限から可算形状の局所左 Kan 余極限を得る。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：有限段階の反対単体圏から元の局所左 Kan 形状への比較。
方針：段階のコンマ圏への逆比較と二つの形状同型を合成する。
規約：指定された自然数の頂点を保持する。使われ方：局所図式の余極限の縮約。 -/
def countableStageKanComparison (B : SSet.{u}) [Countable B.S] (n : ℕ) :
    (SSet.uliftFunctor.{u + 1, u}).obj
      (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableFiniteStage B n).toSSet)ᵒᵖ) ⟶
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape ((SSet.uliftFunctor.{u + 1, u}).map
          (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableSimplexStageFunctor B)))
            (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up n))) :=
  (SSet.uliftFunctor.{u + 1, u}).map
    (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableStageSimplexToComma B n) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableSimplexStageFunctor B) (ULift.up n)).hom) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.leftKanShapeUniverseIso (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableSimplexStageFunctor B))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up n))).hom

/-- 概要：有限段階から局所左 Kan 形状への比較は right cofinal。
方針：コンマ圏の同値の随伴から native な cofinal 性を得て形状同型と合成する。
規約：通常の final 性だけで止めない。使われ方：元の局所余錐の比較。 -/
lemma countableStageKanComparison_isRightCofinal (B : SSet.{u}) [Countable B.S] (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (countableStageKanComparison B n) := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableStageSimplexToComma B n)) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nerveMap_isRightCofinal_of_initial_comma
    intro a
    let adj := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableStageCommaEquivalence B n).toAdjunction
    exact ⟨StructuredArrow.mk (adj.unit.app a),
      ⟨mkInitialOfLeftAdjoint (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableStageSimplexToComma B n) adj a⟩⟩
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isRightCofinal_ulift _ (h.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_isIso
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableSimplexStageFunctor B) (ULift.up n)).hom))).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_isIso
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.leftKanShapeUniverseIso (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableSimplexStageFunctor B))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up n))).hom)

/-- 概要：局所左 Kan 比較は元の有限段階の包含への射影を保つ。
方針：二つの形状同型の射影則とコンマ圏の厳密な射影則を合成する。
規約：同型を介さない実際の射の等式。使われ方：制限図式の同定。 -/
lemma countableStageKanComparison_projection (B : SSet.{u}) [Countable B.S] (n : ℕ) :
    countableStageKanComparison B n ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableSimplexStageFunctor B)))
          (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up n))) =
    (SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableFiniteStage B n).ι).op) := by
  rw [countableStageKanComparison, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.leftKanShapeUniverseIso_projection, ← CategoryTheory.Functor.map_comp]
  congr 1
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeIso_hom_projection]
  change nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableStageSimplexToComma B n ⋙
    CostructuredArrow.proj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableSimplexStageFunctor B) (ULift.up n)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableStageSimplexToComma_proj]

/-- 概要：全有限図式に保存余極限があれば段階関手の全局所図式も保存余極限を持つ。
方針：cofinal 比較で有限段階の反対単体圏へ制限し、その局所化を使う。
規約：有限段階の nerve 自体に有限性を仮定しない。
使われ方：有限余極限から可算形状の保存余極限を構成する局所段階。 -/
lemma hasPreservedColimit_countableStage_leftKan
    {X Y : SSet.{u + 1}} [Quasicategory X] [Quasicategory Y] (U : X ⟶ Y)
    (hfin : ∀ (K : SSet.{u + 1}) [K.Finite] (D : K ⟶ X), _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U D)
    (B : SSet.{u}) [Countable B.S]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B.op ⟶ X) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableSimplexStageFunctor B)))
      ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.oppositeSimplexRestriction B) ≫ F)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up n)))) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.hasPreservedColimit_iff_rightCofinalRestriction U _
    (countableStageKanComparison_isRightCofinal B n) _).mpr
  have he : countableStageKanComparison B n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableSimplexStageFunctor B)))
      ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.oppositeSimplexRestriction B) ≫ F)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up n))) =
      (SSet.uliftFunctor.{u + 1, u}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.oppositeSimplexRestriction (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableFiniteStage B n).toSSet) ≫
      ((SSet.uliftFunctor.{u + 1, u}).map
        (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableFiniteStage B n).ι) ≫ F) := by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram]
    rw [← Category.assoc, countableStageKanComparison_projection,
      ← Category.assoc, ← CategoryTheory.Functor.map_comp,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.oppositeSimplexRestriction_naturality, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [he]
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.hasPreservedColimit_iff_oppositeSimplexRestriction U _ _).mp
  have : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableFiniteStage B n).toSSet.op.Finite :=
    ⟨Finite.of_equiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableFiniteStage B n).toSSet.N SSet.N.opEquiv.symm.toEquiv⟩
  have : ((SSet.uliftFunctor.{u + 1, u}).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableFiniteStage B n).toSSet.op).Finite :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.finite_ulift_iff _).mpr inferInstance
  exact hfin _ _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
