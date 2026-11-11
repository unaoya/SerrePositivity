module

public import SerrePositivity.EInfinity.BarrattEccles.HammockGraphComposition
public import SerrePositivity.EInfinity.BarrattEccles.HammockGraphColimit
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.CompositionPairing

/-!
# 元の E 代数の全語の対に整合する合成余錐

概要：任意の可換環上で、全語の遷移に自然な graph の合成と実際の合成余錐を構成。
方針：実際の弱同値へ連結関手の自然性と対の図式の合成余錐を代入する。
規約：二つの余極限の積からの合成と単位則は後続。モデル構造の追加入力は不要。
使われ方：元の E 代数の hammock の豊穣合成の構成。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra MonoidalCategory

namespace SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A]

/-- 同じ元の graph の合成は、左右の全語の遷移に自然。 -/
lemma algebraHammockGraphComposition_naturality {a b a' b' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word}
    (f : a ⟶ a') (g : b ⟶ b') (X Y Z : (operad A).Algebra) :
    (algebraHammockGraphMap A f X Y ⊗ₘ algebraHammockGraphMap A g Y Z) ≫
        algebraHammockGraphComposition A a' b' X Y Z =
      algebraHammockGraphComposition A a b X Y Z ≫
        algebraHammockGraphMap A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap f g) X Z := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphComposition_naturality (weakEquivalences (operad A).Algebra) f g X Y Z

/-- 同じ実際の全語の対の graph の積図式。 -/
def algebraHammockPairDiagram (X Y Z : (operad A).Algebra) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word × _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{u + 1} := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pairDiagram (weakEquivalences (operad A).Algebra) X Y Z

/-- 同じ元の全固定語の合成を成分に持つ、実際の余錐。 -/
def algebraHammockCompositionCocone (X Y Z : (operad A).Algebra) :
    Limits.Cocone (algebraHammockPairDiagram A X Y Z) := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.compositionPairingCocone (weakEquivalences (operad A).Algebra) X Y Z

/-- 元の対の図式の余極限から、同じ元の全語の余極限への合成比較。 -/
def algebraHammockColimitCompositionPairing (X Y Z : (operad A).Algebra) :
    Limits.colimit (algebraHammockPairDiagram A X Y Z) ⟶ algebraHammockColimitGraph A X Z := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitCompositionPairing (weakEquivalences (operad A).Algebra) X Y Z

/-- 元の全語の対で、同じ固定語の合成と標準射を厳密に回収する。 -/
lemma algebraHammockColimitCompositionPairing_fac (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word)
    (X Y Z : (operad A).Algebra) :
    Limits.colimit.ι (algebraHammockPairDiagram A X Y Z) (a, b) ≫
        algebraHammockColimitCompositionPairing A X Y Z =
      algebraHammockGraphComposition A a b X Y Z ≫
        algebraHammockGraphInclusion A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b) X Z := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitCompositionPairing_fac (weakEquivalences (operad A).Algebra) X Y Z a b

end SerrePositivity.EInfinity.BarrattEccles
