module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanInvertible

/-!
概要：豊穣 Hom 内の同型と coherent nerve の辺のホモトピー類の比較。
方針：豊穣 Hom 内の辺を coherent Hom 比較へ写し、連結成分からホモトピー圏へ移す。
規約：入力は局所 Kan な単体的圏。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、Corollary 5.6.0.6（Tag 028T）、strict な逆条件を coherent な可逆性へ移す。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：豊穣 Hom 内で同型な二つの射は coherent nerve のホモトピー圏で同じ射を表す。
方針：同型の順方向の射を辺で表し、coherent Hom 比較の連結成分を使う。
規約：通常の射の豊穣表示の間の同型を入力に取る。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、strict な図式の逆変換から coherent な同値を得る。 -/
lemma coherentNerveEdge_homMk_eq_of_enrichedVertexIso
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)]
    {X Y : C} {f g : X ⟶ Y}
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (SimplicialCategory.homEquiv' X Y f)
      (SimplicialCategory.homEquiv' X Y g)) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g).toTruncated := by
  obtain ⟨a, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ h.hom
  let e : SSet.Edge
      (X := (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y))
      (ULift.up (SimplicialCategory.homEquiv' X Y f))
      (ULift.up (SimplicialCategory.homEquiv' X Y g)) :=
    SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u, v} a)
  have hp := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomPiZeroToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y))
    (SSet.π₀.sound (e.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison X Y)))
  change SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv _ _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison X Y).app _ (ULift.up (SimplicialCategory.homEquiv' X Y f)))) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv _ _
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison X Y).app _ (ULift.up (SimplicialCategory.homEquiv' X Y g)))) at hp
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv _ _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison X Y).app _ (ULift.up (SimplicialCategory.homEquiv' X Y f))) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated := by
    apply SSet.Truncated.Edge.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison_ordinary f
  have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv _ _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison X Y).app _ (ULift.up (SimplicialCategory.homEquiv' X Y g))) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g).toTruncated := by
    apply SSet.Truncated.Edge.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison_ordinary g
  exact (congrArg₂ Eq (congrArg SSet.Truncated.HomotopyCategory.homMk hf)
    (congrArg SSet.Truncated.HomotopyCategory.homMk hg)).mp hp

/-- 概要：豊穣 Hom 内で両側の逆条件を満たす射は coherent nerve の可逆な辺を与える。
方針：比較同型をホモトピー圏の等式へ移し、指定された逆射の辺を逆として使う。
規約：逆条件は豊穣 Hom 内の頂点の同型として入力する。
使われ方：Kerodon §4.6.7（Tag 01LA）、Corollary 5.6.0.6（Tag 028T）、strict な逆変換の coherent な可逆性。 -/
lemma coherentNerveEdge_isInvertible_of_enrichedInverse
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)]
    {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X)
    (hu : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (SimplicialCategory.homEquiv' X X (f ≫ g))
      (SimplicialCategory.homEquiv' X X (𝟙 X)))
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (SimplicialCategory.homEquiv' Y Y (g ≫ f))
      (SimplicialCategory.homEquiv' Y Y (𝟙 Y))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f) := by
  refine ⟨⟨SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g).toTruncated, ?_, ?_⟩⟩
  · calc
      _ = SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (f ≫ g)).toTruncated :=
        (SSet.Truncated.HomotopyCategory.homMk_comp_homMk
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct f g).toTruncated)
      _ = SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (𝟙 X)).toTruncated :=
        coherentNerveEdge_homMk_eq_of_enrichedVertexIso hu
      _ = 𝟙 _ := by simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_id, SSet.Edge.toTruncated_id,
        SSet.Truncated.HomotopyCategory.homMk_id]
  · calc
      _ = SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (g ≫ f)).toTruncated :=
        (SSet.Truncated.HomotopyCategory.homMk_comp_homMk
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct g f).toTruncated)
      _ = SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (𝟙 Y)).toTruncated :=
        coherentNerveEdge_homMk_eq_of_enrichedVertexIso hc
      _ = 𝟙 _ := by simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_id, SSet.Edge.toTruncated_id,
        SSet.Truncated.HomotopyCategory.homMk_id]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
