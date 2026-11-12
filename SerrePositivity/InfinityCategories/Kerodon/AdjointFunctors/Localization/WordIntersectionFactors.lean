module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordIntersection
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordFactorization

/-!
# 元の列の交わりから二つの包含への射

概要：元の列の交わりの包含は、両方の元の包含を通して厳密に因子分解する。
方針：像の包含と単射な語の写像の持ち上げを用いる。
規約：元の語と元の列の写像を保持する。
使われ方：proper 図式の原像の重なりの回収。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ c) (g : b ⟶ c)

def intersectionLeft (hf : Function.Injective f.orderHom) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersection f g ⟶ a :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.factorEmbedding f hf (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion f g) (by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion_range]; exact Set.inter_subset_left)).val

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (intersectionLeft)


def intersectionRight (hg : Function.Injective g.orderHom) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersection f g ⟶ b :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.factorEmbedding g hg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion f g) (by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion_range]; exact Set.inter_subset_right)).val

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (intersectionRight)


lemma intersectionLeft_fac (hf : Function.Injective f.orderHom) :
    intersectionLeft f g hf ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion f g :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.factorEmbedding f hf (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion f g) (by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion_range]; exact Set.inter_subset_left)).property

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (intersectionLeft_fac)


lemma intersectionRight_fac (hg : Function.Injective g.orderHom) :
    intersectionRight f g hg ≫ g = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion f g :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.factorEmbedding g hg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion f g) (by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion_range]; exact Set.inter_subset_right)).property

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (intersectionRight_fac)


lemma intersectionLeft_injective (hf : Function.Injective f.orderHom) :
    Function.Injective (intersectionLeft f g hf).orderHom := by
  intro i j hij
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion_injective f g
  have he := congrArg (fun h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersection f g ⟶ c => h.orderHom i)
    (intersectionLeft_fac f g hf)
  have he' := congrArg (fun h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersection f g ⟶ c => h.orderHom j)
    (intersectionLeft_fac f g hf)
  exact he.symm.trans ((congrArg f.orderHom hij).trans he')

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (intersectionLeft_injective)


lemma intersectionRight_injective (hg : Function.Injective g.orderHom) :
    Function.Injective (intersectionRight f g hg).orderHom := by
  intro i j hij
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion_injective f g
  have he := congrArg (fun h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersection f g ⟶ c => h.orderHom i)
    (intersectionRight_fac f g hg)
  have he' := congrArg (fun h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersection f g ⟶ c => h.orderHom j)
    (intersectionRight_fac f g hg)
  exact he.symm.trans ((congrArg g.orderHom hij).trans he')

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (intersectionRight_injective)


lemma intersection_length_le_left (hf : Function.Injective f.orderHom) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersection f g).length ≤ a.length := by
  simpa only [Fintype.card_fin] using
    Fintype.card_le_of_injective _ (intersectionLeft_injective f g hf)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (intersection_length_le_left)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
