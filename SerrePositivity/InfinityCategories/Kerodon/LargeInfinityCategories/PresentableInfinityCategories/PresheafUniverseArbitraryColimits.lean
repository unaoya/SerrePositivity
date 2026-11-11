module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseColimitShapeReduction
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PresheafUniverseColimits

/-!
概要：指定された前層の宇宙変更は、任意の小さい添字の元の余極限全余錐を保存する。
方針：検証済みの coherent 添字での保存を、全余錐の形状置換による還元へ渡す。
規約：元の添字の quasicategory 性も sifted 性も追加しない。
使われ方：任意の小さい sifted 添字に対する P_Σ 延長の保存性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：元の前層の指定宇宙変更は、任意の小さい添字の指定全余錐の余極限性を保つ。
方針：検証済みの coherent 添字での保存を、全余錐の形状置換による還元へ渡す。
規約：元の添字の quasicategory 性も sifted 性も追加しない。
使われ方：任意の小さい sifted 添字に対する P_Σ 延長の保存性。 -/
lemma presheafUniverseDiagram_map_isColimit_arbitraryShape {I C : SSet.{u}}
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafUniverseDiagram C)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift.{u + 1, u + 2} c)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapUliftCocone_isColimit_of_quasicategoryShapes (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafUniverseDiagram C)
    (fun _ _ D c hc => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafUniverseDiagram_map_isColimit D c hc) D c hc

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
