module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordEmbeddingUniqueness

/-!
# 同じ列の全射を持つ元の語の終域の比較

概要：同じ長さの終域へ同じ列の全射を与えるなら、元の終域の語と射も一致する。
方針：全射性で元の色を回収し、語の等式と全列の外延性を使う。
規約：単射用の像の一意性で代用せず、全射から終域の色を決める。
使われ方：二重の隣接合成後の元の語と全射列の同定。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

lemma target_eq_of_surjective {a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) (g : a ⟶ c)
    (hf : Function.Surjective f.orderHom) (hn : b.length = c.length)
    (hfg : ∀ i, Fin.cast hn (f.orderHom i) = g.orderHom i) :
    ∃ hbc : b = c, f ≫ eqToHom hbc = g := by
  have hbc : b = c := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit.object_ext b c hn (by
    intro j
    obtain ⟨i, rfl⟩ := hf j
    exact (f.direction_eq i).trans ((g.direction_eq i).symm.trans
      (congrArg c.direction (hfg i).symm)))
  refine ⟨hbc, ?_⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.hom_ext
  intro i
  change (eqToHom hbc : b ⟶ c).orderHom (f.orderHom i) = g.orderHom i
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.eqToHom_apply]
  exact hfg i

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (target_eq_of_surjective)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
