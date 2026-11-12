module
public import SerrePositivity.KST.SConstruction.CoherentConstantComparisonEdges
public import SerrePositivity.KST.SConstruction.CoherentComparisonFaceEdges

/-! # 元の保存した標準面の復号辺と恒等辺
概要：保存済みの標準合成面・恒等面を復号し、元の通常射の同じ恒等辺を回収する。
方針：全二単体を保持した辺表示の移送と、一般復号辺の定数計算を合わせる。
規約：元の面を選び直さず、全比較辺の厳密な等号を証明する。
使われ方：二入力比較四面体の実二経路で、元の固定上辺を恒等辺として回収する。
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

/-- 元の同じ恒等合成三角形を、元の通常の恒等射の辺を用いる表示へ移す。 -/
def coherentNerveUnitCompStruct {X Y : C} (f : X ⟶ Y) :
    SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (𝟙 X)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f) :=
  (SSet.Edge.CompStruct.idComp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f)).ofEq
    (congrArg SSet.Edge.edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_id X).symm) rfl rfl

/-- 表示を移しても元の恒等面の全二単体を変更しない。 -/
lemma coherentNerveUnitCompStruct_simplex {X Y : C} (f : X ⟶ Y) :
    (coherentNerveUnitCompStruct f).simplex =
      (SSet.Edge.CompStruct.idComp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f)).simplex := rfl

/-- 元の標準合成面から復号した比較辺全体は、元の合成射の頂点の恒等辺。 -/
lemma coherentNerveCompStruct_decoded_edge {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (coherentTriangleMappingEdge f g (f ≫ g) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct f g)).edge =
      (SSet.Edge.id (SimplicialCategory.homEquiv' X Z (f ≫ g))).edge :=
  eq_of_heq ((coherentTriangleCompositionEdge_heq f g (f ≫ g)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct f g)).symm.trans (coherentNerveCompStruct_comparison_edge_heq f g))

/-- 元の恒等合成面の復号辺全体も、元の同じ通常射の頂点の恒等辺。 -/
lemma coherentNerveUnitCompStruct_decoded_edge {X Y : C} (f : X ⟶ Y) :
    (coherentTriangleMappingEdge (𝟙 X) f f (coherentNerveUnitCompStruct f)).edge =
      (SSet.Edge.id (SimplicialCategory.homEquiv' X Y f)).edge :=
  eq_of_heq ((coherentTriangleCompositionEdge_heq (𝟙 X) f f
    (coherentNerveUnitCompStruct f)).symm.trans
      ((coherentSimplexCompositionEdge_heq (coherentNerveUnitCompStruct_simplex f)
        0 1 2 (by decide) (by decide)).trans (coherentNerveIdComp_comparison_edge_heq f)))

/-- 元の二つの通常射の恒等辺を豊穣合成すると、元の合成射の同じ恒等辺。 -/
lemma simplicialHom_identityEdges_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (SimplicialCategory.sHomComp X Y Z).app (Opposite.op ⦋1⦌)
      ((SSet.Edge.id (SimplicialCategory.homEquiv' X Y f)).edge,
        (SSet.Edge.id (SimplicialCategory.homEquiv' Y Z g)).edge) =
      (SSet.Edge.id (SimplicialCategory.homEquiv' X Z (f ≫ g))).edge := by
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' X Y f) 1 =
      (SSet.Edge.id (SimplicialCategory.homEquiv' X Y f)).edge := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one _
  have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' Y Z g) 1 =
      (SSet.Edge.id (SimplicialCategory.homEquiv' Y Z g)).edge := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one _
  have hfg : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' X Z (f ≫ g)) 1 =
      (SSet.Edge.id (SimplicialCategory.homEquiv' X Z (f ≫ g))).edge := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one _
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_constant_comp f g 1
  rw [hf, hg, hfg] at ht
  exact ht

end SerrePositivity.KST.SConstruction
