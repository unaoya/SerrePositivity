module
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionReplacementTetrahedron
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EnrichedHomotopy

/-! # 元の豊穣比較辺を面に保持する coherent 合成三角形
概要：長辺から二辺の合成への元の豊穣辺を、同じ比較面を持つ coherent 四面体へ移す。
方針：coherent Hom 比較で元の辺全体を pinched 三角形へ写し、元の合成面と貼る。
規約：成分・類だけの一致に置換せず、元の比較面と標準合成面を全体として保持する。
使われ方：元の BF 境界円柱を入力二射の coherent な実合成面にする。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 元の豊穣辺を全体として coherent Hom 比較で写した同じ pinched 実辺。 -/
def enrichedComparisonPinchedEdge {X Z : C} {f g : X ⟶ Z}
    (e : (SimplicialCategory.sHom X Z).Edge
      (SimplicialCategory.homEquiv' X Z f) (SimplicialCategory.homEquiv' X Z g)) :=
  (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u, v} e.toTruncated)).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison X Z)

/-- 元の豊穣辺の全 pinched 単体を保ち、同じ二射を比較する実三角形。 -/
def enrichedComparisonPinchedTriangle {X Z : C} {f g : X ⟶ Z}
    (e : (SimplicialCategory.sHom X Z).Edge
      (SimplicialCategory.homEquiv' X Z f) (SimplicialCategory.homEquiv' X Z g)) :
    SSet.Edge.CompStruct (SSet.Edge.id (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f) :=
  (SSet.Edge.CompStruct.ofTruncated
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomEdge_compStruct (enrichedComparisonPinchedEdge e))).ofEq rfl
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison_ordinary g) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison_ordinary f)

/-- 比較面の全二単体は、元の豊穣辺の同じ pinched 単体そのもの。 -/
lemma enrichedComparisonPinchedTriangle_simplex {X Z : C} {f g : X ⟶ Z}
    (e : (SimplicialCategory.sHom X Z).Edge
      (SimplicialCategory.homEquiv' X Z f) (SimplicialCategory.homEquiv' X Z g)) :
    (enrichedComparisonPinchedTriangle e).simplex = (enrichedComparisonPinchedEdge e).edge.val :=
  rfl

/-- 元の豊穣比較辺を面に保持し、元の二射と長辺の実合成面を取り出す。 -/
def enrichedCompositionReplacement {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (e : (SimplicialCategory.sHom X Z).Edge
      (SimplicialCategory.homEquiv' X Z h) (SimplicialCategory.homEquiv' X Z (f ≫ g)))
    [Quasicategory (SimplicialNerve C)] :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.compositionReplacementTetrahedron (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct f g)
    (enrichedComparisonPinchedTriangle e)

end SerrePositivity.KST.SConstruction
