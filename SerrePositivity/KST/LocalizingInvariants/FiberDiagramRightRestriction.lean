module

public import SerrePositivity.KST.LocalizingInvariants.FiberSquareRightUniqueness
public import SerrePositivity.KST.LocalizingInvariants.FiberDiagramPrism

/-!
概要：実 fiber 図式間の射は、右辺の全関手としての比較から一意に決まる。
方針：元の射を表す prism に、零 cospan と普遍錐の制限の忠実性を適用する。
規約：任意の fiber 図式の射を扱う。使われ方：模型比較の fiber 頂点成分との照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.FiberDiagram

def rightRestriction : FiberDiagram.{u} ⥤
    hoFunctor.obj ((ihom (Δ[1] : SSet.{u + 1})).obj Sp.{u}) where
  obj D := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ D.triangle.square))
  map f := homPre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge f
  map_id _ := CategoryTheory.Functor.map_id _ _
  map_comp _ _ := CategoryTheory.Functor.map_comp _ _ _

lemma rightRestriction_map_homotopy {D E : FiberDiagram.{u}} (f : D ⟶ E) :
    rightRestriction.map f = Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge (comparisonHomotopy f))) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homMk_functorEdge_precomp, comparisonHomotopy_hom]
  rfl

lemma rightRestriction_map_injective {D E : FiberDiagram.{u}} {f g : D ⟶ E}
    (h : rightRestriction.map f = rightRestriction.map g) : f = g := by
  have he := FiberSquareHomotopy.homMk_eq_of_right D.triangle E.triangle D.isFiber E.isFiber
    (comparisonHomotopy f) (comparisonHomotopy g) (by
      rw [comparisonHomotopy_hom, comparisonHomotopy_hom]
      exact h)
  rw [comparisonHomotopy_hom, comparisonHomotopy_hom] at he
  exact he

instance rightRestriction_faithful : rightRestriction.{u}.Faithful where
  map_injective := fun h ↦ rightRestriction_map_injective h

lemma vertex_map_eq_of_right {D E : FiberDiagram.{u}} {f g : D ⟶ E}
    (h : rightRestriction.map f = rightRestriction.map g) (i j : Fin 2) :
    (vertex i j).map f = (vertex i j).map g :=
  congrArg (fun k ↦ (vertex i j).map k) (rightRestriction_map_injective h)

end SerrePositivity.KST.LocalizingInvariants.FiberDiagram
