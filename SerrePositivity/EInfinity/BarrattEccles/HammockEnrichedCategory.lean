module

public import SerrePositivity.EInfinity.BarrattEccles.HammockColimitUnit
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory

/-!
# 任意の可換環上の元の E 代数の hammock 豊穣圏

概要：元の全語の余極限と連結を、単体的豊穣圏へ束ねる。
方針：構成済みの全公理へ、実際の E 代数の弱同値を代入する。
規約：モデル構造を局所的に選び、追加のモデル入力や大域 instance は要求しない。
使われ方：同じ元の Map^h と DK Hom の高次比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra MonoidalCategory

namespace SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A]

/-- 元の三つの余極限の積からの同じ実際の合成の結合則。 -/
lemma algebraHammockColimitComposition_assoc (X Y Z V : (operad A).Algebra) :
    (algebraHammockColimitComposition A X Y Z ⊗ₘ 𝟙 (algebraHammockColimitGraph A Z V)) ≫
        algebraHammockColimitComposition A X Z V =
      (α_ (algebraHammockColimitGraph A X Y) (algebraHammockColimitGraph A Y Z)
        (algebraHammockColimitGraph A Z V)).hom ≫
          (𝟙 (algebraHammockColimitGraph A X Y) ⊗ₘ algebraHammockColimitComposition A Y Z V) ≫
            algebraHammockColimitComposition A X Y V := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition_assoc (weakEquivalences (operad A).Algebra) X Y Z V

/-- 任意の可換環上の、元の E 代数と全語の余極限による実際の単体的豊穣圏。 -/
@[instance_reducible]
def algebraHammockEnrichedCategory : EnrichedCategory SSet.{u + 1} (operad A).Algebra := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory (weakEquivalences (operad A).Algebra)

/-- 豊穣 Hom は同じ元の全語の実際の余極限。 -/
lemma algebraHammockEnrichedCategory_hom (X Y : (operad A).Algebra) :
    (algebraHammockEnrichedCategory A).Hom X Y = algebraHammockColimitGraph A X Y := rfl

/-- 豊穣単位は同じ元の空語からの単位射。 -/
lemma algebraHammockEnrichedCategory_id (X : (operad A).Algebra) :
    (algebraHammockEnrichedCategory A).id X = algebraHammockColimitUnit A X := rfl

/-- 豊穣合成は同じ元の二つの余極限の積からの合成。 -/
lemma algebraHammockEnrichedCategory_comp (X Y Z : (operad A).Algebra) :
    (algebraHammockEnrichedCategory A).comp X Y Z =
      algebraHammockColimitComposition A X Y Z := rfl

/-- 元の全固定語の三つの標準射の積は、実際の三重積からの射を一意に決める。 -/
lemma algebraHammockTensorTriple_hom_ext (X Y Z V : (operad A).Algebra) {K : SSet.{u + 1}}
    (f g : (algebraHammockColimitGraph A X Y ⊗ algebraHammockColimitGraph A Y Z) ⊗
      algebraHammockColimitGraph A Z V ⟶ K)
    (h : ∀ a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word,
      ((algebraHammockGraphInclusion A a X Y ⊗ₘ algebraHammockGraphInclusion A b Y Z) ⊗ₘ
        algebraHammockGraphInclusion A c Z V) ≫ f =
      ((algebraHammockGraphInclusion A a X Y ⊗ₘ algebraHammockGraphInclusion A b Y Z) ⊗ₘ
        algebraHammockGraphInclusion A c Z V) ≫ g) : f = g := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.tensorTriple_hom_ext (weakEquivalences (operad A).Algebra) X Y Z V f g h

end SerrePositivity.EInfinity.BarrattEccles
