module

public import SerrePositivity.InfinityCategories.ModelBridge.PaddedThreeWeakComparison
public import SerrePositivity.InfinityCategories.ModelBridge.PaddingColimitComparison

/-!
# 元の三列の標準射の後の padding 比較の弱同値性

概要：元の標準射と padding 比較の合成は弱ホモトピー同値となる。
方針：既存の比較ホモトピーを全 Kan 標的への Hom の π₀ 関手で検査する。
規約：任意の弱同値が anodyne 局所化で反転するとは仮定しない。
使われ方：padding の左逆と元の三列の標準射の弱同値性の回収。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory HomotopicalAlgebra SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{v} C] [ModelCategory C] (X Y : C)
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))

include cof in
lemma threeArrowPaddingComposite_isWeakHomotopyEquivalence : IsWeakHomotopyEquivalence
    (graphInclusion (weakEquivalences C) X Y Word.threeArrow ≫
      paddingColimitMap (graphDiagram (weakEquivalences C) X Y)) := by
  intro Z hZ
  have he := ThreeArrow.Padding.colimit_comparison_image_eq X Y
    (FrameHom.AnodyneWeakDetection.homComponents Z).rightOp
    (FrameHom.AnodyneWeakDetection.homComponents_inverts Z)
  have he' := congrArg Quiver.Hom.unop he
  change (FrameHom.AnodyneWeakDetection.homComponents Z).map
      (paddedThreeComparison (graphDiagram (weakEquivalences C) X Y)).op =
    (FrameHom.AnodyneWeakDetection.homComponents Z).map
      (graphInclusion (weakEquivalences C) X Y Word.threeArrow ≫
        paddingColimitMap (graphDiagram (weakEquivalences C) X Y)).op at he'
  change Function.Bijective ((FrameHom.AnodyneWeakDetection.homComponents Z).map
    (graphInclusion (weakEquivalences C) X Y Word.threeArrow ≫
      paddingColimitMap (graphDiagram (weakEquivalences C) X Y)).op)
  rw [← he']
  exact paddedThreeComparison_isWeakHomotopyEquivalence X Y cof Z

end SerrePositivity.EInfinity.Hammock
