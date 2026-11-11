module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore

/-!
# forward 部分語の元の像と交わり

概要：forward 部分語の写像の像は元の列の像への所属を反映し、交わりを保つ。
方針：元の包含への因子分解と色の保存から原像も forward であることを回収する。
規約：全写像の像を扱い、交わりの等式に単射性を追加しない。
使われ方：forward 部分語で前合成した図式の proper 性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

lemma forwardMap_apply_fac {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) (i : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardCore a).length) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusion b).orderHom ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardMap f).orderHom i) =
      f.orderHom ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusion a).orderHom i) :=
  congrArg (fun g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardCore a ⟶ b => g.orderHom i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardMap_fac f)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (forwardMap_apply_fac)


lemma forwardMap_injective {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) (hf : Function.Injective f.orderHom) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardMap f).orderHom := by
  intro i j hij
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusion_injective a
  apply hf
  rw [← forwardMap_apply_fac, ← forwardMap_apply_fac, hij]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (forwardMap_injective)


lemma forwardMap_range_iff {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) (j : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardCore b).length) :
    j ∈ Set.range (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardMap f).orderHom ↔
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusion b).orderHom j ∈ Set.range f.orderHom := by
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusion a).orderHom i, (forwardMap_apply_fac f i).symm⟩
  · rintro ⟨i, hi⟩
    have hd : a.direction i = .forward := (f.direction_eq i).symm.trans
      ((congrArg b.direction hi).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardCore_direction b j))
    obtain ⟨k, hk⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusion_range a i).2 hd
    refine ⟨k, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusion_injective b ?_⟩
    rw [forwardMap_apply_fac, hk, hi]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (forwardMap_range_iff)


lemma forwardMap_intersection_range {a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ c) (g : b ⟶ c) :
    Set.range (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion f g)).orderHom =
      Set.range (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardMap f).orderHom ∩ Set.range (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardMap g).orderHom := by
  ext j
  simp only [Set.mem_inter_iff, forwardMap_range_iff, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion_range]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (forwardMap_intersection_range)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
