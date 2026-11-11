module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GraphIntersection
public import SerrePositivity.EInfinity.Hammock.GraphEmbedding

/-!
# 全語の図式の proper 性と元の像の交わりの比較

概要：Dwyer–Kan §4.4 の包含の単射性と像の交わりの条件を束ねる。
方針：元の部分複体の等式から、交わりへの標準包含の同型性も得る。
規約：filtered 性や単体集合のモデル構造は仮定しない。
使われ方：§5.4 の元の graph 図式と、proper 図式の余極限の不変性。
-/

@[expose] public section
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory

/-- Dwyer–Kan §4.4 の全語の図式の proper 性。 -/
structure ProperDiagram (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{w}) : Prop where
  map_mono {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) (hf : Function.Injective f.orderHom) : Mono (F.map f)
  intersection_range {a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ c) (g : b ⟶ c)
    (hf : Function.Injective f.orderHom) (hg : Function.Injective g.orderHom) :
    Subfunctor.range (F.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion f g)) =
      Subfunctor.range (F.map f) ⊓ Subfunctor.range (F.map g)

lemma imageHomOfLe_isIso {K : SSet.{w}} {A B : K.Subcomplex} (h : A = B) :
    IsIso (Subfunctor.homOfLe (le_of_eq h)) := by
  cases h
  change IsIso (𝟙 A.toFunctor)
  infer_instance

namespace ProperDiagram
variable {F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{w}} (hF : ProperDiagram F) {a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word}
  (f : a ⟶ c) (g : b ⟶ c) (hf : Function.Injective f.orderHom) (hg : Function.Injective g.orderHom)

/-- 交わりの語の像から、元の二つの部分複体の交わりへの標準包含。 -/
def intersectionComparison :
    (Subfunctor.range (F.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion f g))).toFunctor ⟶
      (Subfunctor.range (F.map f) ⊓ Subfunctor.range (F.map g)).toFunctor :=
  Subfunctor.homOfLe (le_of_eq (hF.intersection_range f g hf hg))

/-- 元の標準包含そのものが同型。 -/
lemma intersectionComparison_isIso : IsIso (intersectionComparison hF f g hf hg) :=
  imageHomOfLe_isIso (hF.intersection_range f g hf hg)

/-- 元の交わりへの比較は、元の全単体の包含を保持する。 -/
lemma intersectionComparison_fac :
    intersectionComparison hF f g hf hg ≫
        (Subfunctor.range (F.map f) ⊓ Subfunctor.range (F.map g)).ι =
      (Subfunctor.range (F.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion f g))).ι :=
  Subfunctor.homOfLe_ι _

end ProperDiagram

/-- 元の全語の graph 図式は proper。 -/
lemma graphDiagram_proper {C : Type u} [Category.{v} C] (W : MorphismProperty C)
    [W.IsMultiplicative] (X Y : C) : ProperDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y) where
  map_mono f hf := graphDiagram_map_mono W f hf X Y
  intersection_range f g hf hg := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphDiagram_intersection_range f g hf hg

end SerrePositivity.EInfinity.Hammock
