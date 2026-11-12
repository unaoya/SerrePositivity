module

public import SerrePositivity.EInfinity.BarrattEccles.HammockGraphEmbeddingRange
public import SerrePositivity.EInfinity.BarrattEccles.HammockGraphColimit
public import SerrePositivity.EInfinity.Hammock.ProperDiagram

/-!
# 任意の可換環上の元の E 代数の graph 図式の proper 性

概要：元の対象の回収・全単体の像の交わり・proper 性を任意の可換環上で証明する。
方針：実際の弱同値を恒等列の条件と構成済みの原像へ代入する。
規約：モデル構造を局所的に選び、モデルの追加入力や対象の cofibrancy は不要。
使われ方：元の全語の余極限の不変性と縮約 hammock との比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.EInfinity.BarrattEccles
variable (A : Type u) [CommRing A]

def algebraHammockIdentityOutside {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b)
    (X Y : (operad A).Algebra) (R : algebraHammockZigzag A b X Y) : Prop := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityOutside f R

/-- 元の恒等列の条件から、同じ元の原像の対象を構成する。 -/
def algebraHammockIdentityPreimage {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b)
    (hf : Function.Injective f.orderHom) (X Y : (operad A).Algebra)
    (R : algebraHammockZigzag A b X Y) (hR : algebraHammockIdentityOutside A f X Y R) :
    algebraHammockZigzag A a X Y := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityPreimageObjects.obj f hf R hR

lemma algebraHammockIdentityPreimage_image {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b)
    (hf : Function.Injective f.orderHom) (X Y : (operad A).Algebra)
    (R : algebraHammockZigzag A b X Y) (hR : algebraHammockIdentityOutside A f X Y R) :
    (algebraHammockTransition A f X Y).obj (algebraHammockIdentityPreimage A f hf X Y R hR) =
      R := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityPreimage.obj_image f hf R hR

lemma algebraHammockTransition_obj_range_iff {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b)
    (hf : Function.Injective f.orderHom) (X Y : (operad A).Algebra)
    (R : algebraHammockZigzag A b X Y) :
    R ∈ Set.range (algebraHammockTransition A f X Y).obj ↔
      algebraHammockIdentityOutside A f X Y R := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj_range_iff f hf R

lemma algebraHammockGraphMap_range_iff_identityOutside {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b)
    (hf : Function.Injective f.orderHom) (X Y : (operad A).Algebra) (n : SimplexCategoryᵒᵖ)
    (τ : (algebraHammockGraph A b X Y).obj n) :
    τ ∈ Set.range ((algebraHammockGraphMap A f X Y).app n) ↔
      ∀ j, algebraHammockIdentityOutside A f X Y (τ.obj j) := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphDiagram_map_range_iff_identityOutside f hf n τ

/-- 元の実際の E 代数の全語の図式は、Dwyer–Kan §4.4 の意味で proper。 -/
lemma algebraHammockGraphDiagram_proper (X Y : (operad A).Algebra) :
    Hammock.ProperDiagram (algebraHammockGraphDiagram A X Y) := by
  let := modelCategory A
  exact Hammock.graphDiagram_proper (weakEquivalences (operad A).Algebra) X Y

lemma algebraHammockGraphIntersection_range {a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ c) (g : b ⟶ c)
    (hf : Function.Injective f.orderHom) (hg : Function.Injective g.orderHom)
    (X Y : (operad A).Algebra) :
    Subfunctor.range ((algebraHammockGraphDiagram A X Y).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion f g)) =
      Subfunctor.range ((algebraHammockGraphDiagram A X Y).map f) ⊓
        Subfunctor.range ((algebraHammockGraphDiagram A X Y).map g) :=
  (algebraHammockGraphDiagram_proper A X Y).intersection_range f g hf hg

/-- 原典の像の交わりへの、元の標準包含による比較そのもの。 -/
def algebraHammockGraphIntersectionComparison {a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word}
    (f : a ⟶ c) (g : b ⟶ c)
    (hf : Function.Injective f.orderHom) (hg : Function.Injective g.orderHom)
    (X Y : (operad A).Algebra) :
    (Subfunctor.range ((algebraHammockGraphDiagram A X Y).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion f g))).toFunctor ⟶
        (Subfunctor.range ((algebraHammockGraphDiagram A X Y).map f) ⊓
          Subfunctor.range ((algebraHammockGraphDiagram A X Y).map g)).toFunctor :=
  Hammock.ProperDiagram.intersectionComparison (algebraHammockGraphDiagram_proper A X Y) f g hf hg

lemma algebraHammockGraphIntersectionComparison_isIso {a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word}
    (f : a ⟶ c) (g : b ⟶ c)
    (hf : Function.Injective f.orderHom) (hg : Function.Injective g.orderHom)
    (X Y : (operad A).Algebra) :
    IsIso (algebraHammockGraphIntersectionComparison A f g hf hg X Y) :=
  Hammock.ProperDiagram.intersectionComparison_isIso (algebraHammockGraphDiagram_proper A X Y)
    f g hf hg

lemma algebraHammockGraphIntersectionComparison_fac {a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word}
    (f : a ⟶ c) (g : b ⟶ c)
    (hf : Function.Injective f.orderHom) (hg : Function.Injective g.orderHom)
    (X Y : (operad A).Algebra) :
    algebraHammockGraphIntersectionComparison A f g hf hg X Y ≫
        (Subfunctor.range ((algebraHammockGraphDiagram A X Y).map f) ⊓
          Subfunctor.range ((algebraHammockGraphDiagram A X Y).map g)).ι =
      (Subfunctor.range ((algebraHammockGraphDiagram A X Y).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion f g))).ι :=
  Hammock.ProperDiagram.intersectionComparison_fac (algebraHammockGraphDiagram_proper A X Y)
    f g hf hg

end SerrePositivity.EInfinity.BarrattEccles
