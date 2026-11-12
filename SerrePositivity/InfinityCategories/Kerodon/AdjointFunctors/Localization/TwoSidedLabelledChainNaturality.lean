module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedLabelledChain

/-!
# 元の両端ラベルの射列の全作用素・係数との整合性

概要：底の列と両端ラベルからの復元は全単体作用素と両係数の自然変換に両立する。
方針：元の端点までの区間の合成則と二つの自然性の正方形を評価する。
規約：端の作用素も含め、元の始終点のラベルの移送を明示する。
使われ方：DK §9.5・10.6の二方向 bar の元の行の自然性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory Opposite

variable {W : Type u} [Category.{u} W] (F : Wᵒᵖ ⥤ Type u) (G : W ⥤ Type u)
  {n : ℕ} (c : ComposableArrows W n)
  (a : F.obj (op (c.obj (Fin.last n)))) (b : G.obj (c.obj 0))

lemma lift_reindex {m : ℕ} (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    (SimplexCategory.toCat.map θ).toFunctor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedLabelledChain.lift F G c a b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedLabelledChain.lift F G ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)
        (F.map (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))).op a)
        (G.map (c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0)))) b) := by
  refine CategoryTheory.Functor.ext (fun i => ?_) ?_
  · refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedLabelledChain.element_ext F G _ _ rfl (heq_of_eq ?_) (heq_of_eq ?_)
    · change F.map (c.map (homOfLE (Fin.le_last (θ.toOrderHom i)))).op a =
        F.map (c.map (homOfLE (θ.toOrderHom.monotone (Fin.le_last i)))).op
          (F.map (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))).op a)
      rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp, ← c.map_comp]
      rfl
    · change G.map (c.map (homOfLE (Fin.zero_le (θ.toOrderHom i)))) b =
        G.map (c.map (homOfLE (θ.toOrderHom.monotone (Fin.zero_le i))))
          (G.map (c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0)))) b)
      rw [← ConcreteCategory.comp_apply, ← G.map_comp, ← c.map_comp]
      rfl
  · intro i j h
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.hom_ext F G
    simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedLabelledChain.lift, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.hom_comp_base, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedLabelledChain.eqToHom_base]

lemma lift_map {F' : Wᵒᵖ ⥤ Type u} {G' : W ⥤ Type u} (α : F ⟶ F') (β : G ⟶ G') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedLabelledChain.lift F G c a b ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.map α β =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedLabelledChain.lift F' G' c (α.app (op (c.obj (Fin.last n))) a) (β.app (c.obj 0) b) := by
  refine CategoryTheory.Functor.ext (fun i => ?_) ?_
  · refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedLabelledChain.element_ext F' G' _ _ rfl (heq_of_eq ?_) (heq_of_eq ?_)
    · exact ConcreteCategory.congr_hom
        (α.naturality (c.map (homOfLE (Fin.le_last i))).op) a
    · exact ConcreteCategory.congr_hom
        (β.naturality (c.map (homOfLE (Fin.zero_le i)))) b
  · intro i j h
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.hom_ext F' G'
    simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedLabelledChain.lift, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.hom_comp_base, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedLabelledChain.eqToHom_base]
    rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
