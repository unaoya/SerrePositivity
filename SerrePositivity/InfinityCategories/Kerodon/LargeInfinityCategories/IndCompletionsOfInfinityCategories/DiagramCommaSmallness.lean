module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.DiagramComma
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.CommaSimplexSmallness

/-!
概要：元の全図式 comma の実際の単体は小さい宇宙に属する。
方針：Space∞ の固定頂点符号化を前層・Ind・全図式へ伝え、comma に適用する。
規約：小ささを仮定しない。使われ方：実同型による小さい図式表示添字。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

local instance uliftObjectSmall (A : SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    Small.{u} (((SSet.uliftFunctor.{u + 1, u}).obj A).obj n) :=
  inferInstanceAs (Small.{u} (ULift.{u + 1} (A.obj n)))

/-- 元の Ind 圏への固定頂点の全写像は小さい。 -/
lemma ind_hasSmallFixedVertexMaps (κ : Cardinal.{u}) (C : SSet.{u}) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasSmallFixedVertexMaps (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) := by
  haveI : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf κ C) :=
    inferInstanceAs (Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsIndVertex κ C)).ι)
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasSmallFixedVertexMaps (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.space_hasSmallFixedVertexMaps.functorSpace ((SSet.uliftFunctor.{u + 1, u}).obj C.op)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasSmallFixedVertexMaps.of_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf κ C) h

/-- 元の Ind 全図式圏への固定頂点の全写像も小さい。 -/
lemma indDiagram_hasSmallFixedVertexMaps (κ : Cardinal.{u}) (K C : SSet.{u})
    [Quasicategory C] : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasSmallFixedVertexMaps
      ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj K)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)) :=
  (ind_hasSmallFixedVertexMaps κ C).functorSpace ((SSet.uliftFunctor.{u + 1, u}).obj K)

/-- 指定された元の全 Ind 図式への comma は各次数で小さい。 -/
instance diagramComma_obj_small (κ : Cardinal.{u}) {K C : SSet.{u}} [Quasicategory C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)
    (n : SimplexCategoryᵒᵖ) : Small.{u} ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramComma κ D).obj n) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.leftKanShape_obj_small_of_fixedVertexMaps (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramYoneda κ K C) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D)
    (indDiagram_hasSmallFixedVertexMaps κ K C) n

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
