module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendFixed

/-!
# 指定射の往復を単位列へ比較する二列の hammock

概要：元の指定射とその逆向きの列の合成を恒等列へ比較する。
方針：接合点だけに元の指定射を置き、両端を恒等射に固定する。
規約：元の指定射の逆射の存在は要求しない。
使われ方：hammock での前後合成のホモトピー逆。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {X Y : C} (g : X ⟶ Y) (hg : W g)

def sourceRoundTrip : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)) X X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj g) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.obj g hg)

def sourceUnit (X : C) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)) X X :=
  sourceRoundTrip (𝟙 X) (W.id_mem X)

def targetRoundTrip : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)) Y Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.obj g hg) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj g)

def targetUnit (Y : C) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)) Y Y :=
  targetRoundTrip (𝟙 Y) (W.id_mem Y)

def sourceCancellation : sourceUnit (W := W) X ⟶ sourceRoundTrip g hg := by
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.movingHom (W := W) (e := 𝟙 X) (e' := g)
    (𝟙 X) g (W.id_mem X) hg (by simp)
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.movingHom (W := W) (e := 𝟙 X) (e' := g)
    (W.id_mem X) hg g (𝟙 X) hg (W.id_mem X) (by simp)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedMap f b (HEq.rfl) (by change 𝟙 X = eqToHom _; simp)
    (by change 𝟙 X = eqToHom _; simp)

def targetCancellation : targetRoundTrip g hg ⟶ targetUnit (W := W) Y := by
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.movingHom (W := W) (e := g) (e' := 𝟙 Y)
    hg (W.id_mem Y) (𝟙 Y) g (W.id_mem Y) hg (by simp)
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.movingHom (W := W) (e := g) (e' := 𝟙 Y)
    g (𝟙 Y) hg (W.id_mem Y) (by simp)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedMap b f (HEq.rfl) (by change 𝟙 Y = eqToHom _; simp)
    (by change 𝟙 Y = eqToHom _; simp)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
