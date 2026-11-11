module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.StrictCoherentNatTrans
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Edges
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorNaturalityTriangles

/-!
概要：通常の自然変換の一つの射への全制限を、元の二つの厳密合成三角形へ同定する。
方針：同じ円柱の二つの二単体を通常の nerve で計算し、coherent 表示を後合成する。
規約：二単体の全作用を保つ。使われ方：厳密 cospan 比較の全右辺表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.StrictArrow

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]
  {F G : I ⥤ C} (η : F ⟶ G) {i j : I} (k : i ⟶ j)

def shape : (Δ[1] : SSet.{max u v}) ⟶ (SSet.uliftFunctor.{v, u}).obj (nerve I) :=
  SSet.yonedaEquiv.symm (ULift.up (ComposableArrows.mk₁ k))

def prism : (Δ[1] : SSet.{max u v}) ⊗ Δ[1] ⟶ SimplicialNerve C :=
  (β_ Δ[1] Δ[1]).hom ≫ (Δ[1] ◁ shape k) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap η

lemma lower : SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ prism η k) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (F.map k) (η.app j)).simplex := by
  unfold prism _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap
  rw [← Category.assoc, ← Category.assoc, SSet.yonedaEquiv_comp]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C).app (Opposite.op ⦋2⦌) _ =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C).app (Opposite.op ⦋2⦌) (ComposableArrows.mk₂ (F.map k) (η.app j))
  apply congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C).app (Opposite.op ⦋2⦌))
  refine ComposableArrows.ext₂ rfl rfl rfl ?_ ?_
  · change 𝟙 _ ≫ F.map k = 𝟙 _ ≫ F.map k ≫ 𝟙 _
    simp
  · change η.app j ≫ G.map (𝟙 j) = 𝟙 _ ≫ η.app j ≫ 𝟙 _
    simp

lemma upper : SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ prism η k) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (η.app i) (G.map k)).simplex := by
  unfold prism _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap
  rw [← Category.assoc, ← Category.assoc, SSet.yonedaEquiv_comp]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C).app (Opposite.op ⦋2⦌) _ =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C).app (Opposite.op ⦋2⦌) (ComposableArrows.mk₂ (η.app i) (G.map k))
  apply congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C).app (Opposite.op ⦋2⦌))
  refine ComposableArrows.ext₂ rfl rfl rfl ?_ ?_
  · change η.app i ≫ G.map (𝟙 i) = 𝟙 _ ≫ η.app i ≫ 𝟙 _
    simp
  · change 𝟙 _ ≫ G.map k = 𝟙 _ ≫ G.map k ≫ 𝟙 _
    simp

end SerrePositivity.KST.LocalizingInvariants.StrictArrow
