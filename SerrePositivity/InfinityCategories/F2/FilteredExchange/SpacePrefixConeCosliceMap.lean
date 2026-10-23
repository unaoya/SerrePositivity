module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpacePrefixConeCosliceSimplex

/-!
概要：元の全 cone の prefix 変形を、tail と区間上の実 coslice 射へ組み立てる。
方針：各単体と時刻に同じ変形を作用させ、添字変換の式で自然性を示す。
規約：始点と全 cone の実座標を固定する。
使われ方：零面の全係数族の指定比較円柱。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- prefix 変形による固定始点の実 coslice 円柱。 -/
def spacePrefixConeCosliceMap {n : ℕ} (s : SpaceInfinity.{u} _⦋n + 1⦌) :
    (Δ[n] : SSet.{u + 1}) ⊗ Δ[1] ⟶
      sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex (s.obj ⟨ULift.up 0⟩))) where
  app d := ↾fun ⟨a, t⟩ ↦ spacePrefixConeCosliceSimplex s a.down.toOrderHom t.down.toOrderHom
  naturality {d e} r := by
    apply ConcreteCategory.hom_ext
    rintro ⟨a, t⟩
    exact (spacePrefixConeCosliceSimplex_reindex s a.down.toOrderHom t.down.toOrderHom
      r.unop).symm

end SerrePositivity.InfinityCategories.F2
