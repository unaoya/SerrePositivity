module

public import SerrePositivity.KST.LocalizingInvariants.StrictConeCoherentPrism
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PrismHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentEdges

/-!
概要：大きい添字圏上の coherent prism の各垂直辺を、元の自然変換の成分と同定する。
方針：二点の関手の垂直射を計算し、coherent nerve への同じ一単体の像を使う。
規約：成分の射を選び直さない。使われ方：fiber 錐の頂点射と図式射の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.LocalizingInvariants.StrictConeMap

variable {J : Type (max u v)} [SmallCategory J]
  {C : Type v} [Category.{u} C] [SimplicialCategory C]

omit [SimplicialCategory C] in
lemma largeNervePrism_component {F G : J ⥤ C} (η : F ⟶ G) (j : J) :
    (largeNervePrism η).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (ComposableArrows.mk₀ j) 1) = ComposableArrows.mk₁ (η.app j) := by
  refine ComposableArrows.ext₁ ?_ ?_ ?_
  · rfl
  · rfl
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change η.app j ≫ G.map (𝟙 j) = η.app j
    simp

lemma largeCoherentPrism_component {F G : J ⥤ C} (η : F ⟶ G) (j : J) :
    (largeCoherentPrism η).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (ComposableArrows.mk₀ j) 1) = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (η.app j)).edge := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C).app _ ((largeNervePrism η).app _ _) = _
  rw [largeNervePrism_component]
  rfl

def largeHomotopy {F G : J ⥤ C} (η : F ⟶ G) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.resizedNerveMap F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.resizedNerveMap G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.prismHomotopy (largeCoherentPrism η) (largeCoherentPrism_zero η) (largeCoherentPrism_one η)

lemma largeHomotopy_component {F G : J ⥤ C} (η : F ⟶ G) (j : J) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (largeHomotopy η) (ComposableArrows.mk₀ j)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (η.app j)).edge := by
  rw [largeHomotopy, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.prismHomotopy_vertical]
  exact largeCoherentPrism_component η j

end SerrePositivity.KST.LocalizingInvariants.StrictConeMap
