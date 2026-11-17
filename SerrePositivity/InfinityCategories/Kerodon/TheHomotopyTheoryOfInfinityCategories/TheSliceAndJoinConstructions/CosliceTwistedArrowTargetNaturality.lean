module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceTwistedArrowTarget

/-! 同じ両端交換の、指定された元の関手への厳密な自然性。 -/

@[expose] public section
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 同じ両端交換は任意の元の関手と厳密に可換。 -/
lemma twistedArrowOppositeSwap_naturality {C D : SSet.{u}} (F : C ⟶ D) :
    edgewiseSubdivisionMap (SSet.opFunctor.map F) ≫ twistedArrowOppositeSwap D =
      twistedArrowOppositeSwap C ≫ edgewiseSubdivisionMap F := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro g
  change (edgewiseWeightReverseIso n.unop).inv ≫
      SSet.opFunctor.map (g ≫ SSet.opFunctor.map F) ≫
        (SSet.opFunctorCompOpFunctorIso.app D).hom =
    ((edgewiseWeightReverseIso n.unop).inv ≫ SSet.opFunctor.map g ≫
      (SSet.opFunctorCompOpFunctorIso.app C).hom) ≫ F
  rw [SSet.opFunctor.map_comp]
  have hn : SSet.opFunctor.map (SSet.opFunctor.map F) ≫
      (SSet.opFunctorCompOpFunctorIso.app D).hom =
        (SSet.opFunctorCompOpFunctorIso.app C).hom ≫ F :=
    SSet.opFunctorCompOpFunctorIso.hom.naturality F
  simp only [Category.assoc]
  rw [hn]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
end
