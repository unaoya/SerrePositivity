module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalMoving
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendFixed

/-!
# 相対自然変換の外側の二列と固定端点の行

概要：[id,F(S),ηY] と [ηX,G(S),id] を同じ語の行として構成する。
方針：外側の元の射と中間の元の全成分を動く接合点で貼る。
規約：全体の端点だけを FX,GY に固定する。
使われ方：固定語の比較自然変換。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  {F G : LocalizerMorphism W V} (η : F.functor ⟶ G.functor)
  (hη : ∀ X, V (η.app X)) {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

def beforeRow (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag V (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append w (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)))
      (F.functor.obj X) (G.functor.obj Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (𝟙 (F.functor.obj X)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj F S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (η.app Y)))

def afterRow (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag V (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append w (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)))
      (F.functor.obj X) (G.functor.obj Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (η.app X))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj G S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (𝟙 (G.functor.obj Y))))

def leftEdge (X : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := V) (𝟙 (F.functor.obj X)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (η.app X)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.movingHom (𝟙 (F.functor.obj X)) (η.app X)
    (V.id_mem _) (hη X) (by simp)

def rightEdge (Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := V) (η.app Y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (𝟙 (G.functor.obj Y))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.movingHom (η.app Y) (𝟙 (G.functor.obj Y))
    (hη Y) (V.id_mem _) (by simp)

def innerHom (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalMoving.movingHom η hη S) (rightEdge η hη Y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalMoving.movingHom_last η hη S)

omit [W.IsMultiplicative] in
lemma innerHom_first (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) :
    HEq ((innerHom η hη S).app 0) (η.app X) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_left_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalMoving.movingHom η hη S) (rightEdge η hη Y) 0).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalMoving.movingHom_first η hη S)

omit [W.IsMultiplicative] in
lemma innerHom_last (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) :
    HEq ((innerHom η hη S).app (Fin.last (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append w (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)).length))
      (𝟙 (G.functor.obj Y)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_right_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalMoving.movingHom η hη S) (rightEdge η hη Y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalMoving.movingHom_last η hη S) (Fin.last (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward).length)

def component (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) : beforeRow η S ⟶ afterRow η S :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedMap (leftEdge η hη X) (innerHom η hη S)
    (innerHom_first η hη S).symm
    (by change 𝟙 (F.functor.obj X) = eqToHom _; simp)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.last_of_heq_id _ (innerHom_last η hη S))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows
