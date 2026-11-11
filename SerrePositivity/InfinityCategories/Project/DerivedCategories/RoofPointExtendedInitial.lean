module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofPointExtendedInjection

/-! # 始点だけを零へ送る順序写像の終点固定延長

概要：正番号頂点を零へ潰さない条件は、終点固定延長の後も保持される。
方針：追加終点と元の正番号頂点を分けて、延長の値を計算する。
規約：単射性を仮定しない。使われ方：over 細分と正番号退化の可換性。
-/
@[expose] public section
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory
open scoped _root_.Simplicial

/-- 正番号を零へ送らない条件は、終点固定延長によって保存される。 -/
lemma roofPointExtend_initial {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (hz : ∀ i, i ≠ 0 → α.toOrderHom i ≠ 0) (j : Fin (m + 2)) (hj : j ≠ 0) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α).toOrderHom j ≠ 0 := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom j ≠ 0
  induction j using Fin.lastCases with
  | last => rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last]; simp
  | cast j =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc]
    exact Fin.castSucc_ne_zero_iff.mpr (hz j (Fin.castSucc_ne_zero_iff.mp hj))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
