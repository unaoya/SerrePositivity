module

public import SerrePositivity.InfinityCategories.F2.CoherentPrefixConeSimplex
public import SerrePositivity.InfinityCategories.F2.CoherentPrefixMinimalTime

/-!
概要：固定始点の prefix 円柱の時刻一は元の同じ cone の制限。
方針：始点だけが零時刻であることを使って追加区間を除く。
規約：元の全 cone と実 path をそのまま保持する。
使われ方：零面の指定比較円柱の元の実族側の端点。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 時刻一の固定始点の prefix 単体は元の cone の実際の制限。 -/
lemma coherentPrefixConeSimplex_one {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {m n : ℕ} (s : (SimplicialNerve C) _⦋n + 1⦌)
    (a : Fin (m + 1) →o Fin (n + 1)) :
    coherentPrefixConeSimplex s a (OrderHom.const _ 1) =
      (SimplicialThickening.functor (prependOrderHom a).uliftMap).comp SSet s := by
  unfold coherentPrefixConeSimplex
  rw [coherentPrefixPathDeformationEnriched_eq_of_zero_minimal]
  intro k hk
  rcases k with ⟨k⟩
  induction k using Fin.cases with
  | zero => rfl
  | succ k =>
    change (1 : Fin 2) = 0 at hk
    exact False.elim ((by decide : (1 : Fin 2) ≠ 0) hk)

end SerrePositivity.InfinityCategories.F2
