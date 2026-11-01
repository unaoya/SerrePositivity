module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ForwardZigzag
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.BackwardZigzag
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingAppendFixed

/-!
# 指定射の往復を単位列へ比較する二列の hammock

概要：元の指定射とその逆向きの列の合成を恒等列へ比較する。
方針：接合点だけに元の指定射を置き、両端を恒等射に固定する。
規約：元の指定射の逆射の存在は要求しない。
使われ方：hammock での前後合成のホモトピー逆。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.WeakArrow
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {X Y : C} (g : X ⟶ Y) (hg : W g)

def sourceRoundTrip : Zigzag W
    (Word.append (Word.single .forward) (Word.single .backward)) X X :=
  ZigzagAppend.obj (ForwardZigzag.obj g) (BackwardZigzag.obj g hg)

def sourceUnit (X : C) : Zigzag W
    (Word.append (Word.single .forward) (Word.single .backward)) X X :=
  sourceRoundTrip (𝟙 X) (W.id_mem X)

def targetRoundTrip : Zigzag W
    (Word.append (Word.single .backward) (Word.single .forward)) Y Y :=
  ZigzagAppend.obj (BackwardZigzag.obj g hg) (ForwardZigzag.obj g)

def targetUnit (Y : C) : Zigzag W
    (Word.append (Word.single .backward) (Word.single .forward)) Y Y :=
  targetRoundTrip (𝟙 Y) (W.id_mem Y)

def sourceCancellation : sourceUnit (W := W) X ⟶ sourceRoundTrip g hg := by
  let f := ForwardZigzag.movingHom (W := W) (e := 𝟙 X) (e' := g)
    (𝟙 X) g (W.id_mem X) hg (by simp)
  let b := BackwardZigzag.movingHom (W := W) (e := 𝟙 X) (e' := g)
    (W.id_mem X) hg g (𝟙 X) hg (W.id_mem X) (by simp)
  exact ZigzagAppend.Moving.fixedMap f b (HEq.rfl) (by change 𝟙 X = eqToHom _; simp)
    (by change 𝟙 X = eqToHom _; simp)

def targetCancellation : targetRoundTrip g hg ⟶ targetUnit (W := W) Y := by
  let b := BackwardZigzag.movingHom (W := W) (e := g) (e' := 𝟙 Y)
    hg (W.id_mem Y) (𝟙 Y) g (W.id_mem Y) hg (by simp)
  let f := ForwardZigzag.movingHom (W := W) (e := g) (e' := 𝟙 Y)
    g (𝟙 Y) hg (W.id_mem Y) (by simp)
  exact ZigzagAppend.Moving.fixedMap b f (HEq.rfl) (by change 𝟙 Y = eqToHom _; simp)
    (by change 𝟙 Y = eqToHom _; simp)

end SerrePositivity.EInfinity.Hammock.WeakArrow
