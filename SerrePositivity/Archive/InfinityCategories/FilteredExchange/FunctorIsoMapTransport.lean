module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorSpaceDown

/-!
概要：指定関手同型の両端表示の等式補正は、任意の通常の関手による指定像を保つ。
方針：明示した二端点の等式だけを消去する。
規約：元の指定値を保持。使われ方：宇宙下降前の端点補正と合成の交換。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v w z
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 明示した関手の両端の補正は、任意の宇宙の通常の圏への指定像を型付きで保つ。 -/
lemma mapIso_functorIsoOfEq_heq {X Y : SSet.{u}} {D : Type v} [Category.{w} D]
    (P : ((ihom X).obj Y).HomotopyCategory ⥤ D) {f g f' g' : X ⟶ Y}
    (e : FunctorIso f g) (hf : f = f') (hg : g = g') :
    HEq (P.mapIso (functorIsoOfEq e hf hg)) (P.mapIso e) := by
  subst f' g'
  rfl

/-- 大きい二射の表示を明示して下降した指定同型は、同じ通常の下降関手の像に一致。 -/
lemma functorIsoDown_ofEq_heq_mapIso {X Y : SSet.{u}} [Quasicategory Y] {f g : X ⟶ Y}
    {f' g' : (SSet.uliftFunctor.{z, u}).obj X ⟶ (SSet.uliftFunctor.{z, u}).obj Y}
    (e : FunctorIso f' g') (hf : f' = (SSet.uliftFunctor.{z, u}).map f)
    (hg : g' = (SSet.uliftFunctor.{z, u}).map g) :
    HEq (functorIsoDown (functorIsoOfEq e hf hg))
      ((functorSpaceDown.{u, z} X Y).mapIso e) := by
  rw [functorIsoDown_eq_mapIso]
  exact mapIso_functorIsoOfEq_heq _ _ _ _

end SerrePositivity.InfinityCategories.F2
