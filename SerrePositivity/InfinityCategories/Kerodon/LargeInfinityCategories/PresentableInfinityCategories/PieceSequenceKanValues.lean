module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceFiberKan
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallShapeLeftKanExtension
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallPartialColimitFamily

/-!
概要：部分 poset 列の全空間に沿う Kan 拡張の値を、元の指定段の実余極限として回収する。
方針：共終な fiber 比較を宇宙持ち上げし、局所普遍余錐を制限する。
規約：Kan 延長の値そのものを厳密な余錐頂点とする。使われ方：交互細分列の余極限族。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceKanValues

local instance : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩
variable {μ : Cardinal.{u}} {J : Type u} [PartialOrder J]

/-- 元の fiber 比較を、同じ大きい局所 Kan 添字へ持ち上げる。 -/
def pieceSequenceFiberKanComparisonUniverse
    (A : ℕ → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J) (n : ℕ) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve (A n).val) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal.pieceSequenceTotalIndex A)))
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up n))) :=
  (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceFiberKan.pieceSequenceFiberKanComparison A n) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.leftKanShapeUniverseIso _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up n))).hom

/-- 同じ大きい局所比較は right cofinal。 -/
lemma pieceSequenceFiberKanComparisonUniverse_isRightCofinal
    (A : ℕ → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J) (hA : Monotone A) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (pieceSequenceFiberKanComparisonUniverse A n) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isRightCofinal_ulift _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceFiberKan.pieceSequenceFiberKanComparison_isRightCofinal A hA n)).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_trivialKanFibration
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.leftKanShapeUniverseIso _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up n))).hom)

/-- 元の大きい局所比較も、全空間の指定 fiber 包含を厳密に回収する。 -/
lemma pieceSequenceFiberKanComparisonUniverse_projection
    (A : ℕ → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J) (n : ℕ) :
    pieceSequenceFiberKanComparisonUniverse A n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal.pieceSequenceTotalIndex A)))
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up n))) =
        (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal.pieceSequenceTotalFiber A n)) := by
  dsimp only [pieceSequenceFiberKanComparisonUniverse]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.leftKanShapeUniverseIso_projection,
    ← Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceFiberKan.pieceSequenceFiberKanComparison_projection]

/-- 指定された全 Kan 延長の値を、同じ段の実余極限頂点として回収する。 -/
lemma pieceSequence_leftKan_value_isPartialColimit
    (A : ℕ → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J) (hA : Monotone A)
    {C : SSet.{u + 1}} [Quasicategory C]
    {F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal.PieceSequenceTotal A)) ⟶ C}
    {G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶ C}
    {β : SSet.Homotopy F
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal.pieceSequenceTotalIndex A)) ≫ G)}
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal.pieceSequenceTotalIndex A))) F G β)
    (n : ℕ) :
    ∃ a : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal.pieceSequenceTotalFiber A n)) ≫ F),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone a ∧ a.vertex = G.app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up n))) := by
  obtain ⟨c, hc, hv⟩ := hβ.colimitValue (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up n)))
  let q := pieceSequenceFiberKanComparisonUniverse A n
  have hq := pieceSequenceFiberKanComparisonUniverse_isRightCofinal A hA n
  have hd := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal q hq c).mp hc
  have he : q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal.pieceSequenceTotalIndex A))) F
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up n))) =
      (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal.pieceSequenceTotalFiber A n)) ≫ F := by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram]
    rw [← Category.assoc, pieceSequenceFiberKanComparisonUniverse_projection]
  refine ⟨_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq he (c.restrict q),
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_isColimit_iff he _).mp hd, ?_⟩
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_restrict]
  exact hv

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceKanValues
