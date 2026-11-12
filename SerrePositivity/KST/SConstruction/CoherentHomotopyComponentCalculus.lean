module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.StrictConeFunctorImage
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomotopyComposition
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation

/-! # Coherent な円柱と実三角形の成分の計算
概要：後合成と合成三角形を、同じ円柱から取り出した元の一単体へ厳密に戻す。
方針：nerve の自然性と、関手空間の二単体の頂点での評価を使う。
規約：三辺を選び直さず、計算に quasicategory 性を仮定しない。
使われ方：collage 内の合成した成分と元の固定構造射の類の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 豊穣関手の nerve は元の通常の射の辺を、元の通常の作用の辺へ写す。 -/
lemma enrichedNerveMap_edge {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    (R : EnrichedFunctor SSet.{u} C D) {X Y : C} (f : X ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap R).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R).map f)).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_edge, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_edge]
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent_postcomp R) (Opposite.op ⦋1⦌))
    (ComposableArrows.mk₁ f)
  simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply, nerveMap_app_mk₁] using h

/-- 通常の図式の豊穣後合成は、各頂点で元の対象の像を回収する。 -/
lemma strictCoherentDiagram_postcomp_vertex {C D : Type v}
    [Category.{u} C] [Category.{u} D] [SimplicialCategory C] [SimplicialCategory D]
    {I : Type u} [SmallCategory I] (F : I ⥤ C)
    (R : EnrichedFunctor SSet.{u} C D) (i : I) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap R).app (Opposite.op ⦋0⦌)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (R.obj (F.obj i)) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap R).app _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F).app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i))) = _
  exact (congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap R).app (Opposite.op ⦋0⦌))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_vertex F i)).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex R (F.obj i))

/-- 円柱の後合成は、対象での元の成分の一単体をそのまま写す。 -/
lemma homotopyVertexEdge_postcomp {A X Y : SSet.{u}} {f g : A ⟶ X}
    (H : SSet.Homotopy f g) (q : X ⟶ Y) (a : A _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H q) a).edge =
      q.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H a).edge := rfl

/-- 円柱を curry して頂点で評価すると、同じ元の成分の辺になる。 -/
lemma homotopyVertexEdge_yoneda {A X : SSet.{u}} {f g : A ⟶ X}
    (H : SSet.Homotopy f g) (a : A _⦋0⦌) :
    SSet.yonedaEquiv (curry H.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H a).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex]
  change H.h.app (Opposite.op ⦋1⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant a 1, SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) = _
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge := by
    apply SSet.stdSimplex.ext
    intro k
    fin_cases k <;> rfl
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one, hi]
  rfl

/-- 全体の指定三辺の実三角形は、各頂点で同じ三辺の実三角形を与える。 -/
def homotopyCompositionTriangle_vertex {A X : SSet.{u}} {f g h : A ⟶ X}
    (l : SSet.Homotopy f g) (r : SSet.Homotopy g h) (d : SSet.Homotopy f h)
    (T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d) (a : A _⦋0⦌) :
    SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge l a)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge r a) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge d a) := by
  refine SSet.Edge.CompStruct.mk (SSet.yonedaEquiv (T.diagram ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a)) ?_ ?_ ?_
  · rw [← SSet.stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, T.face_two]
    exact homotopyVertexEdge_yoneda l a
  · rw [← SSet.stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, T.face_zero]
    exact homotopyVertexEdge_yoneda r a
  · rw [← SSet.stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, T.face_one]
    exact homotopyVertexEdge_yoneda d a

/-- 全体三角形の成分の合成は、同じ成分のホモトピー圏の射の類での合成。 -/
lemma homotopyCompositionTriangle_vertex_hom {A X : SSet.{u}} {f g h : A ⟶ X}
    (l : SSet.Homotopy f g) (r : SSet.Homotopy g h) (d : SSet.Homotopy f h)
    (T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d) (a : A _⦋0⦌) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge l a).toTruncated ≫
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge r a).toTruncated =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge d a).toTruncated :=
  SSet.Truncated.HomotopyCategory.homMk_comp_homMk
    (homotopyCompositionTriangle_vertex l r d T a).toTruncated

end SerrePositivity.KST.SConstruction
