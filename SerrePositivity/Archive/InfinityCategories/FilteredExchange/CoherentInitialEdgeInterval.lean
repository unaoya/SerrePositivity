module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentPrefixTargetMap
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentPrefixConeSimplex

/-!
概要：最初の二頂点への包含は、その二頂点間の区間を全て写す。
方針：元の有限頂点の全ての順序関係を直接計算する。
規約：比較三単体の同じ初二頂点を使う。
使われ方：全係数円柱の始点を元の恒等辺へ制限する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.F2

/-- 比較三単体の最初の二頂点への包含。 -/
def coherentInitialEdgeObjects : ULift.{u} (Fin 2) →o ULift.{u} (Fin 4) :=
  (prependOrderHom (OrderHom.const (Fin 1) (0 : Fin 3))).uliftMap

/-- 最初の二頂点への包含は全区間を写す。 -/
lemma coherentInitialEdgeObjects_interval
    (x y : ULift.{u} (Fin 2)) (z : ULift.{u} (Fin 4)) :
    coherentInitialEdgeObjects x ≤ z → z ≤ coherentInitialEdgeObjects y →
      ∃ w : ULift.{u} (Fin 2), x ≤ w ∧ w ≤ y ∧ coherentInitialEdgeObjects w = z := by
  rcases x with ⟨x⟩
  rcases y with ⟨y⟩
  rcases z with ⟨z⟩
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    simp only [ULift.exists, Fin.exists_fin_succ, Fin.exists_fin_zero] <;> decide

end SerrePositivity.InfinityCategories.F2
