module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordEmbeddingUniqueness

/-!
# forward 部分語の固定対象と一列への元の合成

概要：全方向 forward の語では元の部分語包含は同型であり、一列への射は唯一である。
方針：元の列の像の全射性と包含の一意性、Fin 1 の一意性を使う。
規約：空語の一列への射を含む。元の語の等式と包含の射を同時に回収する。
使われ方：forward 部分語で前合成した図式の余極限の回収。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

lemma forwardInclusion_eqToHom (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (ha : ∀ i, a.direction i = .forward) :
    ∃ h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardCore a = a, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusion a = eqToHom h := by
  have hr : Set.range (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusion a).orderHom = Set.range (𝟙 a : a ⟶ a).orderHom := by
    ext i
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusion_range]
    exact iff_of_true (ha i) ⟨i, rfl⟩
  obtain ⟨h, hh⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.embedding_eq_of_range (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusion a) (𝟙 a)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusion_injective a) Function.injective_id hr
  exact ⟨h, by simpa only [Category.comp_id] using hh.symm⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (forwardInclusion_eqToHom)


lemma forwardInclusion_isIso (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (ha : ∀ i, a.direction i = .forward) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusion a) := by
  obtain ⟨h, he⟩ := forwardInclusion_eqToHom a ha
  rw [he]
  infer_instance

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (forwardInclusion_isIso)


lemma forwardMap_forwardInclusion (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusion a) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardCore a) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusion_cancel
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardMap_fac (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusion a)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (forwardMap_forwardInclusion)


lemma forwardMap_forwardInclusion_isIso (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusion a)) := by
  rw [forwardMap_forwardInclusion]
  exact forwardInclusion_isIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardCore a) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardCore_direction a)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (forwardMap_forwardInclusion_isIso)


def forwardCollapse (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardCore a ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward where
  orderHom := OrderHom.const _ (0 : Fin 1)
  direction_eq i := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardCore_direction a i).symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (forwardCollapse)


lemma toSingleForward_unique {a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f g : a ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) : f = g := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.hom_ext
  intro i
  exact Subsingleton.elim (α := Fin 1) (f.orderHom i) (g.orderHom i)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (toSingleForward_unique)


lemma forwardCollapse_naturality {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardMap f ≫ forwardCollapse b = forwardCollapse a := toSingleForward_unique _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (forwardCollapse_naturality)


def forwardCollapseNat : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardFunctor ⟶ (Functor.const _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) where
  app := forwardCollapse
  naturality _ _ f := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardMap f ≫ forwardCollapse _ = forwardCollapse _ ≫ 𝟙 _
    rw [Category.comp_id, forwardCollapse_naturality]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (forwardCollapseNat)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
