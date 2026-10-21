module

public import SerrePositivity.EInfinity.Hammock.ZigzagAppendParts
public import SerrePositivity.EInfinity.Hammock.ZigzagMovingHom

/-!
# 元の前後の部分の全縦射

概要：元の全縦弱同値を前後の部分へ制限し、動く接合点の射も保持する。
方針：各位置の同じ成分と元の列の可換正方形を切り出す。
規約：任意の向きの語・空語も含む。
使われ方：局所置換の図式へ貼り合わせる前後の図式。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.ZigzagAppend.Part
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {a b : Word} {X Y : C} {S T : Zigzag W (Word.append a b) X Y}

def leftMap (f : S ⟶ T) : Zigzag.MovingHom (leftObj S) (leftObj T) where
  app i := f.app (Word.leftVertex a b i)
  app_mem _i := f.app_mem _
  comm i := Segment.square_transport f _ _ _ (Word.source_left a b i).symm
    (Word.target_left a b i)

def rightMap (f : S ⟶ T) : Zigzag.MovingHom (rightObj S) (rightObj T) where
  app i := f.app (Word.rightVertex a b i)
  app_mem _i := f.app_mem _
  comm i := Segment.square_transport f _ _ _ (Word.source_right a b i).symm
    (Word.target_right a b i)

end SerrePositivity.EInfinity.Hammock.ZigzagAppend.Part
