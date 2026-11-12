module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverWordNaturality
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordComposition

/-!
# 元の値の fiber の全語の作用の単位と合成

概要：元の全部分圏への制限も厳密な語の作用の単位と合成を保つ。
方針：元の包含による関手の照合を元の語の作用の法則へ戻す。
規約：全部分圏の対象と全射の一致を使う。
使われ方：元の全語の圏値図式。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q) {Y : Paths Q}
  {β : (Quiver.FreeGroupoid.of Q).obj A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.obj Y}

lemma valueFiberFunctor_ext {D : Type u'} [Category.{v'} D] {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word}
    (F G : D ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueFiber A w Y β)
    (h : F ⋙ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagValueProperty A w Y β).ι = G ⋙ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagValueProperty A w Y β).ι) : F = G := by
  have ho : ∀ d, F.obj d = G.obj d := fun d =>
    ObjectProperty.FullSubcategory.ext (CategoryTheory.Functor.congr_obj h d)
  apply CategoryTheory.Functor.hext (F := F) (G := G) ho
  intro d e f
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.valueFiber_hom_hext A (ho d) (ho e) (F.map f) (G.map f)
    (CategoryTheory.Functor.hcongr_hom h f)

lemma zigzagFiberWordAction_id (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberWordAction A Y β (𝟙 w) = 𝟭 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueFiber A w Y β) := by
  apply valueFiberFunctor_ext A
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberWordAction_inclusion, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.functor_id,
    CategoryTheory.Functor.comp_id, CategoryTheory.Functor.id_comp]

lemma zigzagFiberWordAction_comp {a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) (g : b ⟶ c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberWordAction A Y β (f ≫ g) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberWordAction A Y β f ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberWordAction A Y β g := by
  apply valueFiberFunctor_ext A
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagValueProperty A a Y β).ι ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor (f ≫ g) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberWordAction_inclusion A Y β _
    _ = ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagValueProperty A a Y β).ι ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f) ⋙
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor g := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordComposition.functor_comp]; rfl
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberWordAction A Y β f ⋙ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagValueProperty A b Y β).ι) ⋙
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor g := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberWordAction_inclusion]
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberWordAction A Y β f ⋙
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagValueProperty A b Y β).ι ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor g) := rfl
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberWordAction A Y β f ⋙
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberWordAction A Y β g ⋙ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagValueProperty A c Y β).ι) := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberWordAction_inclusion]
    _ = _ := rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
