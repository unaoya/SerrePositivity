module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy

/-!
概要：元の実ホモトピーを両端の厳密な等式で表示し直す。
方針：端点の等式を消去し、実円柱をそのまま保持する。
規約：新しい代表を選ばない。
使われ方：全係数の coslice 円柱を元の pointed 族の両端へ揃える。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 実円柱を保持してホモトピーの両端を等式で表示し直す。 -/
def functorHomotopyOfEndpointEq {X Y : SSet.{u}} {f g f' g' : X ⟶ Y}
    (H : SSet.Homotopy f g) (hf : f = f') (hg : g = g') : SSet.Homotopy f' g' := by
  subst f'
  subst g'
  exact H

/-- 両端の表示を揃えても実円柱は同じ射。 -/
lemma functorHomotopyOfEndpointEq_h {X Y : SSet.{u}} {f g f' g' : X ⟶ Y}
    (H : SSet.Homotopy f g) (hf : f = f') (hg : g = g') :
    (functorHomotopyOfEndpointEq H hf hg).h = H.h := by
  subst f'
  subst g'
  rfl

end SerrePositivity.InfinityCategories.F2
