module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor
public import Mathlib.CategoryTheory.Category.Cat
/-!
# 元の固定端点の相対作用の Cat 値の恒等・合成

概要：相対関手の恒等・合成を、動く始点の係数圏の元の射へ回収する。
方針：元の相対関手の等式で帰納し、既存の固定作用の厳密な関手則を使う。
規約：始点は元の像で動かし、終点表示の等式を保持する。
使われ方：DK10.3の元の係数 transfunctor の恒等・合成則。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory
variable {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  {U : MorphismProperty E} [U.IsMultiplicative] {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word}
lemma fixedFunctor_id_toCatHom_heq (F : LocalizerMorphism W W) (h : F = LocalizerMorphism.id W)
    (X Y : C) (hY : F.functor.obj Y = Y) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor (w := w) F (rfl : F.functor.obj X = F.functor.obj X) hY).toCatHom)
      (𝟙 (Cat.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y))) := by
  cases h
  exact heq_of_eq (congrArg Functor.toCatHom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor_id (W := W) (w := w) (rfl : X = X) hY))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Relative.fixedFunctor_id_toCatHom_heq export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (fixedFunctor_id_toCatHom_heq)


lemma fixedFunctor_comp_toCatHom_heq
    (F : LocalizerMorphism W V) (G : LocalizerMorphism V U) (H : LocalizerMorphism W U)
    (h : H = F.comp G) (X Y : C) (Y' : D) (Y'' : E)
    (hY : F.functor.obj Y = Y') (hY' : G.functor.obj Y' = Y'') (hYH : H.functor.obj Y = Y'') :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor (w := w) H (rfl : H.functor.obj X = H.functor.obj X) hYH).toCatHom)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor (w := w) F (rfl : F.functor.obj X = F.functor.obj X) hY).toCatHom ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor (w := w) G
          (rfl : G.functor.obj (F.functor.obj X) = G.functor.obj (F.functor.obj X))
          hY').toCatHom) := by
  cases h
  exact heq_of_eq (congrArg Functor.toCatHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor_comp (w := w) F G
    (rfl : F.functor.obj X = F.functor.obj X) hY
    (rfl : G.functor.obj (F.functor.obj X) = G.functor.obj (F.functor.obj X)) hY'))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Relative.fixedFunctor_comp_toCatHom_heq export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (fixedFunctor_comp_toCatHom_heq)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
