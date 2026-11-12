module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone

/-!
概要：固定した cone の始点へ時刻零を前置する。
方針：時刻の単調写像に零を加え、元の添字変換と同時に制限する。
規約：元の tail の時刻はそのまま保つ。
使われ方：零面の実 coslice 比較の全次数での定義。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace SerrePositivity.InfinityCategories.F2

/-- 元の時刻へ、cone の固定始点の時刻零を前置する。 -/
def coherentPrefixConeTime {n : ℕ} (t : Fin (n + 1) →o Fin 2) :
    Fin (n + 2) →o Fin 2 where
  toFun := Fin.cases 0 t
  monotone' i j hij := by
    induction i using Fin.cases with
    | zero => exact Fin.zero_le _
    | succ i =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ j => exact t.monotone (Fin.succ_le_succ_iff.mp hij)

/-- cone の時刻の前置は元の tail の添字変換と厳密に可換。 -/
lemma coherentPrefixConeTime_reindex {m n : ℕ}
    (a : Fin (m + 1) →o Fin (n + 1)) (t : Fin (n + 1) →o Fin 2) :
    (coherentPrefixConeTime t).comp (prependOrderHom a) =
      coherentPrefixConeTime (t.comp a) := by
  ext i
  induction i using Fin.cases with
  | zero => rfl
  | succ i => rfl

end SerrePositivity.InfinityCategories.F2
