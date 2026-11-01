module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagAppendPartMaps
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingDiagramFixed

/-!
# 元の前後の語の動く接合点を持つ図式

概要：元の固定端点の zigzag 圏上で左右の部分と接合点を図式にする。
方針：元の全縦射の制限の恒等・合成則と両端の成分回収を使う。
規約：局所接合点の評価関手は定数とは仮定しない。
使われ方：任意の prefix/core/suffix へのモデル圏的置換の接続。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.ZigzagAppend.Part
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {a b : Word} {X Y : C}

def jointFunctor : Zigzag W (Word.append a b) X Y ⥤ C :=
  Zigzag.evaluation (Word.leftVertex a b (Fin.last a.length))

def leftDiagram : Zigzag.MovingDiagram (Zigzag W (Word.append a b) X Y) C W a
    ((Functor.const _).obj X) jointFunctor where
  obj := leftObj
  map := leftMap
  map_id _ := by
    apply Zigzag.MovingHom.ext
    intro j
    rfl
  map_comp _ _ := by
    apply Zigzag.MovingHom.ext
    intro j
    rfl
  first {S T} f := by
    change HEq (f.app 0) (𝟙 X)
    apply (conj_eqToHom_iff_heq _ _ S.first T.first).1
    simpa only [Category.id_comp, eqToHom_trans] using f.first
  last _ := HEq.rfl

def rightDiagram : Zigzag.MovingDiagram (Zigzag W (Word.append a b) X Y) C W b
    jointFunctor ((Functor.const _).obj Y) where
  obj := rightObj
  map := rightMap
  map_id _ := by
    apply Zigzag.MovingHom.ext
    intro j
    rfl
  map_comp _ _ := by
    apply Zigzag.MovingHom.ext
    intro j
    rfl
  first f := Zigzag.app_heq f (Word.jointVertex a b).symm
  last {S T} f := by
    change HEq (f.app (Fin.last (Word.append a b).length)) (𝟙 Y)
    apply (conj_eqToHom_iff_heq _ _ S.last T.last).1
    simpa only [Category.id_comp, eqToHom_trans] using f.last

end SerrePositivity.EInfinity.Hammock.ZigzagAppend.Part
