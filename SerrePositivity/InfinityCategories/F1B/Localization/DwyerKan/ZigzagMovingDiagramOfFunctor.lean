module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingDiagram

/-!
# 元の固定端点の関手から動く局所図式への入口

概要：元の zigzag 圏への任意の関手を、端点が定数である MovingDiagram に移す。
方針：元の全縦射を保持し、first/last の等式から端点成分を回収する。
規約：元の関手を恒等関手にすれば元の固定語の全図式を得る。
使われ方：任意の前後の語を切り出す際の元の graph 圏上の図式。
-/

@[expose] public section
universe u v u' v'
noncomputable section
namespace SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram
open CategoryTheory

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {w : Word} {X Y : C}

def ofFunctor (F : D ⥤ Zigzag W w X Y) :
    MovingDiagram D C W w ((Functor.const D).obj X) ((Functor.const D).obj Y) where
  obj := F.obj
  map f := MovingHom.ofHom (F.map f)
  map_id d := by
    apply MovingHom.ext
    intro i
    change (F.map (𝟙 d)).app i = _
    rw [F.map_id]
    rfl
  map_comp f g := by
    apply MovingHom.ext
    intro i
    change (F.map (f ≫ g)).app i = _
    rw [F.map_comp]
    rfl
  first {d d'} f := by
    change HEq ((F.map f).app 0) (𝟙 X)
    apply (conj_eqToHom_iff_heq _ _ (F.obj d).first (F.obj d').first).1
    simpa only [Category.id_comp, eqToHom_trans] using (F.map f).first
  last {d d'} f := by
    change HEq ((F.map f).app (Fin.last w.length)) (𝟙 Y)
    apply (conj_eqToHom_iff_heq _ _ (F.obj d).last (F.obj d').last).1
    simpa only [Category.id_comp, eqToHom_trans] using (F.map f).last

end SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram
