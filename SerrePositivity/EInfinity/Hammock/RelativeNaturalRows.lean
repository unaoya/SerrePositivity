module

public import SerrePositivity.EInfinity.Hammock.RelativeNaturalMoving
public import SerrePositivity.EInfinity.Hammock.ForwardZigzag
public import SerrePositivity.EInfinity.Hammock.ZigzagMovingAppendFixed

/-!
# 相対自然変換の外側の二列と固定端点の行

概要：[id,F(S),ηY] と [ηX,G(S),id] を同じ語の行として構成する。
方針：外側の元の射と中間の元の全成分を動く接合点で貼る。
規約：全体の端点だけを FX,GY に固定する。
使われ方：固定語の比較自然変換。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.RelativeNatural
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  {F G : LocalizerMorphism W V} (η : F.functor ⟶ G.functor)
  (hη : ∀ X, V (η.app X)) {w : Word} {X Y : C}

def beforeRow (S : Zigzag W w X Y) :
    Zigzag V (Word.append (Word.single .forward) (Word.append w (Word.single .forward)))
      (F.functor.obj X) (G.functor.obj Y) :=
  ZigzagAppend.obj (ForwardZigzag.obj (𝟙 (F.functor.obj X)))
    (ZigzagAppend.obj (Zigzag.Relative.obj F S) (ForwardZigzag.obj (η.app Y)))

def afterRow (S : Zigzag W w X Y) :
    Zigzag V (Word.append (Word.single .forward) (Word.append w (Word.single .forward)))
      (F.functor.obj X) (G.functor.obj Y) :=
  ZigzagAppend.obj (ForwardZigzag.obj (η.app X))
    (ZigzagAppend.obj (Zigzag.Relative.obj G S) (ForwardZigzag.obj (𝟙 (G.functor.obj Y))))

def leftEdge (X : C) :
    Zigzag.MovingHom (ForwardZigzag.obj (W := V) (𝟙 (F.functor.obj X)))
      (ForwardZigzag.obj (η.app X)) :=
  ForwardZigzag.movingHom (𝟙 (F.functor.obj X)) (η.app X)
    (V.id_mem _) (hη X) (by simp)

def rightEdge (Y : C) :
    Zigzag.MovingHom (ForwardZigzag.obj (W := V) (η.app Y))
      (ForwardZigzag.obj (𝟙 (G.functor.obj Y))) :=
  ForwardZigzag.movingHom (η.app Y) (𝟙 (G.functor.obj Y))
    (hη Y) (V.id_mem _) (by simp)

def innerHom (S : Zigzag W w X Y) :=
  ZigzagAppend.Moving.map (movingHom η hη S) (rightEdge η hη Y)
    (movingHom_last η hη S)

omit [W.IsMultiplicative] in
lemma innerHom_first (S : Zigzag W w X Y) :
    HEq ((innerHom η hη S).app 0) (η.app X) :=
  (ZigzagAppend.Moving.app_left_heq (movingHom η hη S) (rightEdge η hη Y) 0).trans
    (movingHom_first η hη S)

omit [W.IsMultiplicative] in
lemma innerHom_last (S : Zigzag W w X Y) :
    HEq ((innerHom η hη S).app (Fin.last (Word.append w (Word.single .forward)).length))
      (𝟙 (G.functor.obj Y)) :=
  ZigzagAppend.Moving.app_right_heq (movingHom η hη S) (rightEdge η hη Y)
    (movingHom_last η hη S) (Fin.last (Word.single .forward).length)

def component (S : Zigzag W w X Y) : beforeRow η S ⟶ afterRow η S :=
  ZigzagAppend.Moving.fixedMap (leftEdge η hη X) (innerHom η hη S)
    (innerHom_first η hη S).symm
    (by change 𝟙 (F.functor.obj X) = eqToHom _; simp)
    (Zigzag.MovingHom.last_of_heq_id _ (innerHom_last η hη S))

end SerrePositivity.EInfinity.Hammock.RelativeNatural
