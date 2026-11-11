module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeWordAction
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitGraph
public import SerrePositivity.EInfinity.Hammock.ReducedColimit
public import Mathlib.CategoryTheory.Category.ULift

/-!
# 元の Hom の ULift による全 zigzag の厳密な比較

概要：同じ対象と全縦横射の up・down で元の全語の graph を同型にする。
方針：Hom の異なる宇宙を全射列で直接比較し、全作用素と語の自然性を保つ。
規約：対象・元の弱同値・全単体を保持する。
使われ方：全代数の hammock を実際の DK 入力と同じ Hom の宇宙へ揃える。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.HomLift
open CategoryTheory CategoryTheory.Limits
variable {C : Type (u + 1)} [Category.{u} C] (W : MorphismProperty C) [W.IsMultiplicative]
def liftedWeak : MorphismProperty (ULiftHom.{u + 1} C) :=
  W.inverseImage (ULiftHom.down.{u, u + 1, u + 1} (C := C))
instance liftedWeak_isMultiplicative : (liftedWeak W).IsMultiplicative := by
  change (W.inverseImage (ULiftHom.down.{u, u + 1, u + 1} (C := C))).IsMultiplicative
  infer_instance
def down : LocalizerMorphism (liftedWeak W) W :=
  ⟨ULiftHom.down.{u, u + 1, u + 1}, fun _ _ _ hf => hf⟩
def up : LocalizerMorphism W (liftedWeak W) :=
  ⟨ULiftHom.up.{u, u + 1, u + 1}, fun _ _ _ hf => hf⟩
variable (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C)
def downFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (liftedWeak W) w (ULiftHom.objUp.{u + 1, u + 1} X) (ULiftHom.objUp.{u + 1,
  u + 1} Y) ⥤
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (down W)
def upFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y ⥤
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (liftedWeak W) w (ULiftHom.objUp.{u + 1, u + 1} X) (ULiftHom.objUp.{u + 1, u + 1} Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (up W)
lemma down_up : downFunctor W w X Y ⋙ upFunctor W w X Y = 𝟭 _ := rfl
lemma up_down : upFunctor W w X Y ⋙ downFunctor W w X Y = 𝟭 _ := rfl
def graphIso : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph (liftedWeak W) w (ULiftHom.objUp.{u + 1, u + 1} X) (ULiftHom.objUp.{u + 1, u +
  1} Y) ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W w X Y where
  hom := { app _ := ↾fun σ => σ ⋙ downFunctor W w X Y
           naturality _ _ _ := rfl }
  inv := { app _ := ↾fun σ => σ ⋙ upFunctor W w X Y
           naturality _ _ _ := rfl }
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro σ
    change (σ ⋙ downFunctor W w X Y) ⋙ upFunctor W w X Y = σ
    rw [CategoryTheory.Functor.assoc, down_up, CategoryTheory.Functor.comp_id]
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro σ
    change (σ ⋙ upFunctor W w X Y) ⋙ downFunctor W w X Y = σ
    rw [CategoryTheory.Functor.assoc, up_down, CategoryTheory.Functor.comp_id]
def graphDiagramIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (liftedWeak W) (ULiftHom.objUp.{u + 1, u + 1} X) (ULiftHom.objUp.{u + 1, u + 1} Y)
      ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y :=
  NatIso.ofComponents (fun w => graphIso W w X Y) (by
    intro a b f
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro σ
    change σ ⋙ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f ⋙ downFunctor W b X Y) =
      σ ⋙ (downFunctor W a X Y ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f)
    exact congrArg (fun H => σ ⋙ H) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeWordAction.wordAction_functor_eq (down W) f).symm)
end SerrePositivity.EInfinity.Hammock.HomLift
