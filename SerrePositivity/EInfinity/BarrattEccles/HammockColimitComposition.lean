module

public import SerrePositivity.EInfinity.BarrattEccles.HammockCompositionPairing
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitComposition

/-!
# 元の E 代数の二つの hammock 余極限の積からの合成

概要：任意の可換環上で、同じ全語の余極限の積から実際の合成を構成する。
方針：元の弱同値に外部積余錐の余極限性と合成の降下を代入する。
規約：モデル構造は構成済みのものを局所的に選び、追加入力を要求しない。
使われ方：元の E 代数の hammock の結合・単位則と豊穣圏の構成。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra MonoidalCategory

namespace SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A]

/-- 対の図式の余極限と、同じ実際の二つの余極限の積との標準同型。 -/
def algebraHammockTensorPairColimitIso (X Y Z : (operad A).Algebra) :
    Limits.colimit (algebraHammockPairDiagram A X Y Z) ≅
      algebraHammockColimitGraph A X Y ⊗ algebraHammockColimitGraph A Y Z := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.tensorPairColimitIso (weakEquivalences (operad A).Algebra) X Y Z

/-- 同じ元の二つの余極限の積を始域とする実際の合成。 -/
def algebraHammockColimitComposition (X Y Z : (operad A).Algebra) :
    algebraHammockColimitGraph A X Y ⊗ algebraHammockColimitGraph A Y Z ⟶
      algebraHammockColimitGraph A X Z := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition (weakEquivalences (operad A).Algebra) X Y Z

/-- 全固定語の元の標準射上で、同じ合成と連結語の標準射を回収する。 -/
lemma algebraHammockColimitComposition_fac (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word)
    (X Y Z : (operad A).Algebra) :
    (algebraHammockGraphInclusion A a X Y ⊗ₘ algebraHammockGraphInclusion A b Y Z) ≫
        algebraHammockColimitComposition A X Y Z =
      algebraHammockGraphComposition A a b X Y Z ≫
        algebraHammockGraphInclusion A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b) X Z := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition_fac (weakEquivalences (operad A).Algebra) X Y Z a b

/-- 同じ標準同型は、元の全固定語の二つの標準射の積を回収する。 -/
lemma algebraHammockTensorPairColimitIso_fac (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word)
    (X Y Z : (operad A).Algebra) :
    Limits.colimit.ι (algebraHammockPairDiagram A X Y Z) (a, b) ≫
        (algebraHammockTensorPairColimitIso A X Y Z).hom =
      (algebraHammockGraphInclusion A a X Y ⊗ₘ algebraHammockGraphInclusion A b Y Z) := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.tensorPairColimitIso_fac (weakEquivalences (operad A).Algebra) X Y Z a b

/-- 前工程の同じ比較は、標準同型と二つの余極限の積からの合成に厳密に分解。 -/
lemma algebraHammockTensorPairColimitIso_comp (X Y Z : (operad A).Algebra) :
    (algebraHammockTensorPairColimitIso A X Y Z).hom ≫
        algebraHammockColimitComposition A X Y Z =
      algebraHammockColimitCompositionPairing A X Y Z := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.tensorPairColimitIso_comp (weakEquivalences (operad A).Algebra) X Y Z

/-- 全固定語の元の標準射の積は、実際の積からの射を一意に決める。 -/
lemma algebraHammockTensorPair_hom_ext (X Y Z : (operad A).Algebra) {K : SSet.{u + 1}}
    (f g : algebraHammockColimitGraph A X Y ⊗ algebraHammockColimitGraph A Y Z ⟶ K)
    (h : ∀ a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word,
      (algebraHammockGraphInclusion A a X Y ⊗ₘ algebraHammockGraphInclusion A b Y Z) ≫ f =
      (algebraHammockGraphInclusion A a X Y ⊗ₘ algebraHammockGraphInclusion A b Y Z) ≫ g) :
    f = g := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.tensorPair_hom_ext (weakEquivalences (operad A).Algebra) X Y Z f g h

end SerrePositivity.EInfinity.BarrattEccles
