module

public import SerrePositivity.EInfinity.Hammock.ZigzagMovingDiagramFixed

/-!
# 動く局所図式と比較の前合成

概要：元の添字圏への関手に沿って局所図式とその比較を制限する。
方針：端点の評価関手も前合成し、元の全縦射と自然性を保持する。
規約：制限後の局所端点も定数とは仮定しない。
使われ方：中央列が自明 cofibration の全部分圏上の右置換。
-/

@[expose] public section
universe u v u' v' u'' v''
noncomputable section
namespace SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram
open CategoryTheory

variable {D : Type u'} [Category.{v'} D] {D' : Type u''} [Category.{v''} D']
  {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {w : Word} {A B : D ⥤ C}

def precomp (F : MovingDiagram D C W w A B) (K : D' ⥤ D) :
    MovingDiagram D' C W w (K ⋙ A) (K ⋙ B) where
  obj d := F.obj (K.obj d)
  map f := F.map (K.map f)
  map_id d := by rw [K.map_id]; exact F.map_id (K.obj d)
  map_comp f g := by rw [K.map_comp]; exact F.map_comp (K.map f) (K.map g)
  first f := F.first (K.map f)
  last f := F.last (K.map f)

def Hom.precomp {F G : MovingDiagram D C W w A B} (h : Hom F G) (K : D' ⥤ D) :
    Hom (F.precomp K) (G.precomp K) where
  app d := h.app (K.obj d)
  naturality f := h.naturality (K.map f)
  first d := h.first (K.obj d)
  last d := h.last (K.obj d)

end SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram
