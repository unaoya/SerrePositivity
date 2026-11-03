module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentMaximalSimplexPrefix
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpacePrefixConeCosliceMap

/-!
概要：最大化表示を tail とする固定始点の coslice 円柱は元の全図式を固定する。
方針：実 coslice 座標の tail を取り、全ての時刻で同じ制限を回収する。
規約：任意の coherent な元の図式を扱い、strict 図式だけに制限しない。
使われ方：零面の全係数比較を同じ図式上の延長空間へ入れる。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 元の tail が最大化図式なら実 coslice 円柱の射影は全時刻で同じ図式。 -/
lemma spacePrefixConeCosliceMap_projection {n : ℕ}
    (s : SpaceInfinity.{u} _⦋n + 1⦌) (r : SpaceInfinity.{u} _⦋n⦌)
    (hr : SpaceInfinity.δ 0 s = coherentSimplexMaximalization r) :
    spacePrefixConeCosliceMap s ≫
      sliceUnderProjection (SSet.yonedaEquiv.symm
        (coherentNerveVertex (s.obj ⟨ULift.up 0⟩))) =
      fst Δ[n] Δ[1] ≫ SSet.yonedaEquiv.symm (coherentSimplexMaximalization r) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨a, t⟩
  exact (coherentCosliceSourceSimplex_tail _
    (spacePrefixConeCosliceSimplex s a.down.toOrderHom t.down.toOrderHom)).symm.trans
      ((congrArg (fun z : SpaceInfinity.{u} _⦋d.unop.len + 1⦌ ↦ SpaceInfinity.δ 0 z)
        (spacePrefixConeCosliceSimplex_coordinates s a.down.toOrderHom t.down.toOrderHom)).trans
          (coherentPrefixConeSimplex_tail_of_maximal s r hr
            a.down.toOrderHom t.down.toOrderHom))

end SerrePositivity.InfinityCategories.F2
