module

public import SerrePositivity.KST.Spectra.PointedHomotopyClasses

/-!
概要：suspension–loop 随伴の逆は点つき射の成分の等式を保つ。
方針：uncurry を suspension と評価の後合成で表示する。
規約：Kan 性を要求しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2。随伴構造射の成分の可換性から構造射の可換性へ戻す。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.PointedMapping

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：loop 値の点つき射の成分の等式は uncurry 後も成分の等式となる。
方針：suspension による成分の等式の保存に評価の後合成を組み合わせる。
規約：標的の Kan 性を要求しない。
使われ方：Goerss–Jardine I §7。随伴を使ったスペクトルの構造可換式の検査。 -/
theorem componentOf_uncurry {X Y : PointedSimplicialSet.{u}}
    {f g : X ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y} (h : componentOf f = componentOf g) :
    componentOf ((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv X Y).symm f) =
      componentOf ((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv X Y).symm g) := by
  change componentOf (MonoidalClosed.uncurry f) = componentOf (MonoidalClosed.uncurry g)
  rw [MonoidalClosed.uncurry_eq, MonoidalClosed.uncurry_eq]
  exact componentOf_comp_right (componentOf_suspension h)
    ((ihom.ev PointedSimplicialSet.circle.{u}).app Y)

/-- 概要：随伴構造射が同じ成分なら元の suspension 構造射も同じ成分。
方針：uncurry の成分の保存と随伴の往復を使う。
規約：構造射自体の厳密な等式を要求しない。
使われ方：BF 1978 §2、HA §1.4.2。ホモトピー可換な列の比較の厳密化の入力。 -/
theorem componentOf_of_curry {X Y : PointedSimplicialSet.{u}}
    {f g : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X ⟶ Y}
    (h : componentOf (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv X Y f) =
      componentOf (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv X Y g)) : componentOf f = componentOf g := by
  simpa only [Equiv.symm_apply_apply] using componentOf_uncurry h

end

end SerrePositivity.KST.Spectra.PointedMapping
