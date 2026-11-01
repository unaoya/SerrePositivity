module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingDiagramHomAppend

/-!
# 全体の両端を固定した図式と自然変換への回収

概要：元の全体の端点が定数なら、動く局所図式の連結から通常の関手を得る。
方針：両端の恒等条件だけを回収し、同じ全頂点の恒等・合成・自然性を使う。
規約：内側の動く局所接合点を固定する必要はない。
使われ方：prefix/core/suffix を貼った後の元の固定端点の zigzag 図式。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram
open CategoryTheory

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {w : Word} {X Y : C}
  (F : MovingDiagram D C W w ((Functor.const D).obj X) ((Functor.const D).obj Y))

def fixedFunctor : D ⥤ Zigzag W w X Y where
  obj := F.obj
  map f := (F.map f).toHom (MovingHom.first_of_heq_id _ (F.first f))
    (MovingHom.last_of_heq_id _ (F.last f))
  map_id d := by
    apply Zigzag.hom_ext
    intro j
    exact congrArg (fun h => h.app j) (F.map_id d)
  map_comp f g := by
    apply Zigzag.hom_ext
    intro j
    exact congrArg (fun h => h.app j) (F.map_comp f g)

namespace Hom
variable {F} {G : MovingDiagram D C W w ((Functor.const D).obj X) ((Functor.const D).obj Y)}
  (h : Hom F G)

def natTrans : F.fixedFunctor ⟶ G.fixedFunctor where
  app d := (h.app d).toHom (MovingHom.first_of_heq_id _ (h.first d))
    (MovingHom.last_of_heq_id _ (h.last d))
  naturality _ _ f := by
    apply Zigzag.hom_ext
    intro j
    exact congrArg (fun k => k.app j) (h.naturality f)

end Hom
end SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram
