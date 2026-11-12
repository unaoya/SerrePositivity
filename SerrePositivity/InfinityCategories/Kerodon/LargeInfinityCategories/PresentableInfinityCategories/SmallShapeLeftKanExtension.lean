module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallPieceLeftKanExtension
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition

/-!
概要：小さい全形状間の写像に沿う、余完備標的への native 左 Kan 拡張を構成する。
方針：公開の局所添字の宇宙同型で小余極限を持ち上げ、点ごとの存在定理を適用する。
規約：大きい形状一般の余完備性を仮定しない。使われ方：増大部分 poset の余極限族。

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


/-- 小さい元の写像の持ち上げに沿う局所 Kan 図式は、同じ小余極限を持つ。 -/
lemma smallShape_leftKanDiagram_hasColimit
    {K L : SSet.{u}} [Quasicategory K] [Quasicategory L] (δ : K ⟶ L)
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C)
    (v : ((SSet.uliftFunctor.{u + 1, u}).obj L) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram ((SSet.uliftFunctor.{u + 1, u}).map δ) F v) := by
  rcases v with ⟨v⟩
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.leftKanShapeUniverseIso.{u, u + 1} δ v
  have he : e.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram ((SSet.uliftFunctor.{u + 1, u}).map δ) F
      (ULift.up v) = (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ v) ≫ F := by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.leftKanShapeUniverseIso_projection]
  have hsmall : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (e.hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram ((SSet.uliftFunctor.{u + 1, u}).map δ) F (ULift.up v)) := by
    rw [he]
    exact hC (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ v) _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.hasColimit_of_equivalentRestriction e.hom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e).isQCatEquivalence _ hsmall

/-- 元の小さい写像に沿う coherent な全左 Kan 拡張が存在する。 -/
lemma exists_smallShape_leftKanExtension
    {K L : SSet.{u}} [Quasicategory K] [Quasicategory L] (δ : K ⟶ L)
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C) :
    ∃ (G : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶ C)
      (β : SSet.Homotopy F ((SSet.uliftFunctor.{u + 1, u}).map δ ≫ G)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension ((SSet.uliftFunctor.{u + 1, u}).map δ) F G β :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftExtension_of_local_colimits _ F
    (smallShape_leftKanDiagram_hasColimit δ hC F)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
