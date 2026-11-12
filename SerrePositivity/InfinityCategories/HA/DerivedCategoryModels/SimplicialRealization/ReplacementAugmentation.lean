module

public import SerrePositivity.HomologicalAlgebra.SimplicialReplacement
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SourceVertexSimplex
import all SerrePositivity.HomologicalAlgebra.SimplicialReplacement
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SourceVertexSimplex

/-!
# Δᵒᵖ の単体的置換から元の単体的対象への自然比較

## 概要
bar の n 本の射列の先頭の値を、先頭頂点単体の作用素で元の n 次の値へ送る。

## 方針
余積の各因子で同じ作用素を使い、任意の単体作用素への自然性を先頭頂点公式から得る。

## 規約
比較は strict な全図式の自然変換。擬同型や native 余極限性はこの段では主張しない。

## 使われ方
HTT 4.2.4.1、HA 1.2.4。bar の射列と単体次数で添字づけた実現を結ぶ実際の比較射。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits Opposite
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open SerrePositivity.HomologicalAlgebra
variable {C : Type u} [Category.{v} C] [HasCoproducts.{0} C]

/-- 元の単体的対象へ戻る比較を、bar の各射列上の同じ単体作用素で定める。 -/
def replacementAugmentation (X : SimplicialObject C) : simplicialReplacement X ⟶ X where
  app n := Sigma.desc (fun s => X.map (sourceVertexSimplex s).op)
  naturality {n m} r := by
    apply Sigma.hom_ext
    intro s
    change Sigma.ι (replacementTerms X n) s ≫ (replacementMap X r ≫ _) = _
    rw [ι_replacementMap_assoc]
    simp only [Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc]
    rw [← X.map_comp, ← X.map_comp]
    exact congrArg (fun t => X.map t.op) (sourceVertexSimplex_whisker s r.unop)

/-- 比較の各因子上の射は、先頭頂点単体の同じ作用素。 -/
@[reassoc (attr := simp)]
theorem ι_replacementAugmentation (X : SimplicialObject C) (n : SimplexCategoryᵒᵖ)
    (s : ComposableArrows SimplexCategoryᵒᵖ n.unop.len) :
    Sigma.ι (replacementTerms X n) s ≫ (replacementAugmentation X).app n =
      X.map (sourceVertexSimplex s).op := Sigma.ι_comp_desc _ _

/-- 比較射は元の全 strict 図式の射に自然。 -/
def replacementAugmentationNatTrans :
    simplicialReplacementFunctor (J := SimplexCategoryᵒᵖ) (C := C) ⟶
      𝟭 (SimplicialObject C) where
  app := replacementAugmentation
  naturality {X Y} η := by
    apply NatTrans.ext
    funext n
    apply Sigma.hom_ext
    intro s
    change Sigma.ι (replacementTerms X n) s ≫
      ((simplicialReplacementMap η).app n ≫ (replacementAugmentation Y).app n) =
      Sigma.ι (replacementTerms X n) s ≫ ((replacementAugmentation X).app n ≫ η.app n)
    rw [ι_simplicialReplacementMap_assoc,
      ι_replacementAugmentation, ι_replacementAugmentation_assoc]
    exact (η.naturality _).symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
