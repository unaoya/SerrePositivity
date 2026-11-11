module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Edges
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderDiagrams
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.StrictCoherentNatTrans
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictNerveMaps
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic

/-!
概要：自然変換の coherent 円柱の成分と図式全体の同型。
方針：垂直辺を指定成分と同定し、点ごとの可逆性を関手の同型へ送る。
規約：対象と Hom の宇宙は異なってよい。
使われ方：Cat_∞ 内の元の cospan と path 置換後の cospan の同値。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]

omit [SimplicialCategory C] in
/-- 概要：通常の nerve の円柱の垂直辺は指定自然変換の成分。
方針：二点の対象と唯一の生成射の像を計算する。
規約：元の成分そのものを等式で回収する。
使われ方：coherent な垂直辺の可逆性の検証。 -/
lemma resizedNatTransMap_component {F G : I ⥤ C} (η : F ⟶ G) (i : I) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.resizedNatTransMap η).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (ULift.up (ComposableArrows.mk₀ i)) 1) =
      ComposableArrows.mk₁ (η.app i) := by
  refine ComposableArrows.ext₁ ?_ ?_ ?_
  · rfl
  · rfl
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change η.app i ≫ G.map (𝟙 i) = η.app i
    simp
/-- 概要：coherent 円柱の垂直辺は指定成分の coherent な辺。
方針：通常の nerve の成分の等式に coherent 表示を適用する。
規約：元の関手の射の辺を選択せずに回収する。
使われ方：成分ごとの同値から図式全体の同型を作る。 -/
lemma strictCoherentNatTransMap_component {F G : I ⥤ C} (η : F ⟶ G) (i : I) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap η).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (ULift.up (ComposableArrows.mk₀ i)) 1) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (η.app i)).edge := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C).app _ ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.resizedNatTransMap η).app _ _) = _
  rw [resizedNatTransMap_component]
  rfl
/-- 概要：各成分が可逆な自然変換の coherent 円柱は全頂点で可逆。
方針：全頂点を元の対象の定値零単体として表示し、垂直辺の式を使う。
規約：元の円柱の一単体自体の可逆性を返す。
使われ方：指定された図式の prism を保つ錐の輸送。 -/
lemma strictCoherentNatTransMap_vertical_isInvertible {F G : I ⥤ C}
    (η : F ⟶ G) (hη : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (η.app i)))
    (x : ((SSet.uliftFunctor.{v, u}).obj (nerve I)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap η).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1))) := by
  have hx : x = ULift.up (ComposableArrows.mk₀ (x.down.obj 0)) := by
    apply ULift.ext
    exact ComposableArrows.ext₀ rfl
  rw [hx, strictCoherentNatTransMap_component]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex _)
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (η.app (x.down.obj 0))) rfl).mpr (hη _)
/-- 概要：各成分が可逆な自然変換は strict coherent 図式の同型を与える。
方針：全頂点を通常の対象として表示し、円柱の垂直辺の可逆性を検証する。
規約：標的 coherent nerve の quasicategory 性を明示する。
使われ方：Cat_∞ の cospan の path 置換の前後の比較。 -/
def strictCoherentNatTransIso [Quasicategory (SimplicialNerve C)] {F G : I ⥤ C}
    (η : F ⟶ G) (hη : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (η.app i))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram G) := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorIsoOfEquivalenceHomotopy (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap η)
    (strictCoherentNatTransMap_vertical_isInvertible η hη)
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap_zero, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap_one] at e
  exact e

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity
