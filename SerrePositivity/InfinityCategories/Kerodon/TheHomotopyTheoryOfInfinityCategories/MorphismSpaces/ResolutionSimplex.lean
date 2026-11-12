module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionFlags

/-!
概要：標準単体上の coherent Hom 比較の補助単体集合と射影。
方針：正規化した有限部分集合の旗を単体とし、各段の最大元を標準単体に写す。
規約：これは明示的な組み合わせ論の模型。比較の同値性は別に証明する。
使われ方：Kerodon Example 4.6.7.27（Tag 01M0）、Construction 4.6.7.22（Tag 01LV）、Proposition 4.6.7.23（Tag 01LW）。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：標準単体の coherent な解像に用いる旗の単体集合。
方針：部分集合の旗を単体とし、最初の段で正規化する引き戻しを作用とする。
規約：ULift によって任意の単体の宇宙 u に配置する。
使われ方：Kerodon Example 4.6.7.27（Tag 01M0）、Φ(Δ[n]) の包含順序に合わせた右模型。 -/
def coherentResolutionSimplex (n : ℕ) : SSet.{u} where
  obj d := ULift.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d.unop.len)
  map α := ↾fun F ↦ ULift.up (F.down.pullback α.unop.toOrderHom)
  map_id d := by
    apply ConcreteCategory.hom_ext
    intro F
    apply ULift.ext
    exact F.down.pullback_id
  map_comp α β := by
    apply ConcreteCategory.hom_ext
    intro F
    apply ULift.ext
    exact (F.down.pullback_comp α.unop.toOrderHom β.unop.toOrderHom).symm

/-- 概要：旗の解像から標準単体への最大元の射影。
方針：各段の最大元が単調であることと、引き戻しに整合することを使う。
規約：同値性の証明を定義に含めない。
使われ方：Kerodon Construction 4.6.7.22（Tag 01LV）、Proposition 4.6.7.23（Tag 01LW） の射影の標準単体での表示。 -/
def coherentResolutionProjection (n : ℕ) : coherentResolutionSimplex.{u} n ⟶ Δ[n] where
  app d := ↾fun F ↦ ULift.up (SimplexCategory.mkHom ⟨F.down.maxAt, F.down.maxAt_monotone⟩)
  naturality {a b} α := by
    apply ConcreteCategory.hom_ext
    intro F
    apply stdSimplex.ext
    intro i
    change (F.down.pullback α.unop.toOrderHom).maxAt i =
      F.down.maxAt (α.unop.toOrderHom i)
    exact F.down.maxAt_pullback α.unop.toOrderHom i

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
