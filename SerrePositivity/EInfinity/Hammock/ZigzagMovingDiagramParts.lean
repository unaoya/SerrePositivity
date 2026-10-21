module

public import SerrePositivity.EInfinity.Hammock.ZigzagAppendParts
public import SerrePositivity.EInfinity.Hammock.ZigzagMovingDiagramEvaluation

/-!
# 動く端点を持つ図式の前後の部分

概要：元の連結語の図式を、動く接合対象を共有する二つの図式に分ける。
方針：各頂点と全縦射を元の左右の位置へ制限する。
規約：二度の分割で任意の prefix/core/suffix を抽出できる。
使われ方：前後の語を保持した局所 MovingFamily の構成。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram
open CategoryTheory

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {a b : Word} {A B : D ⥤ C}
  (F : MovingDiagram D C W (Word.append a b) A B)

def jointFunctor : D ⥤ C := F.evaluation (Word.leftVertex a b (Fin.last a.length))

def leftPartMap {d d' : D} (f : d ⟶ d') :
    MovingHom (ZigzagAppend.Part.leftObj (F.obj d))
      (ZigzagAppend.Part.leftObj (F.obj d')) where
  app i := (F.map f).app (Word.leftVertex a b i)
  app_mem _i := (F.map f).app_mem _
  comm i := (F.map f).square_transport _ _ _ (Word.source_left a b i).symm
    (Word.target_left a b i)

def rightPartMap {d d' : D} (f : d ⟶ d') :
    MovingHom (ZigzagAppend.Part.rightObj (F.obj d))
      (ZigzagAppend.Part.rightObj (F.obj d')) where
  app i := (F.map f).app (Word.rightVertex a b i)
  app_mem _i := (F.map f).app_mem _
  comm i := (F.map f).square_transport _ _ _ (Word.source_right a b i).symm
    (Word.target_right a b i)

def leftPart : MovingDiagram D C W a A F.jointFunctor where
  obj d := ZigzagAppend.Part.leftObj (F.obj d)
  map := F.leftPartMap
  map_id d := by
    apply MovingHom.ext
    intro i
    exact congrArg (fun g => g.app (Word.leftVertex a b i)) (F.map_id d)
  map_comp f g := by
    apply MovingHom.ext
    intro i
    exact congrArg (fun h => h.app (Word.leftVertex a b i)) (F.map_comp f g)
  first f := F.first f
  last _ := HEq.rfl

def rightPart : MovingDiagram D C W b F.jointFunctor B where
  obj d := ZigzagAppend.Part.rightObj (F.obj d)
  map := F.rightPartMap
  map_id d := by
    apply MovingHom.ext
    intro i
    exact congrArg (fun g => g.app (Word.rightVertex a b i)) (F.map_id d)
  map_comp f g := by
    apply MovingHom.ext
    intro i
    exact congrArg (fun h => h.app (Word.rightVertex a b i)) (F.map_comp f g)
  first f := MovingHom.app_heq (F.map f) (Word.jointVertex a b).symm
  last f := F.last f

end SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram
