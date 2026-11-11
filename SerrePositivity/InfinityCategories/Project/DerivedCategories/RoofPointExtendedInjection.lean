module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofPointSliceSimplex

/-! # 終点固定延長は単射性と始点零を保つ

概要：順序単射を追加した終点で延長しても単射で、元の零固定条件を保つ。
方針：追加終点と元の頂点を分け、既存の二つの延長公式を使う。
規約：任意次元。使われ方：over 細分と始点を含む面の可換性。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory
open scoped _root_.Simplicial

/-- 任意の順序単射は、終点固定延長の後にも単射となる。 -/
lemma roofPointExtend_injective {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (hα : Function.Injective α.toOrderHom) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α).toOrderHom := by
  intro i j h
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom i =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom j at h
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rfl
    | cast j =>
      have he : Fin.last (n + 1) = (α.toOrderHom j).castSucc := by
        simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc] using h
      exact (Fin.castSucc_ne_last _ he.symm).elim
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      have he : (α.toOrderHom i).castSucc = Fin.last (n + 1) := by
        simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc] using h
      exact (Fin.castSucc_ne_last _ he).elim
    | cast j =>
      have he : (α.toOrderHom i).castSucc = (α.toOrderHom j).castSucc := by
        simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc] using h
      exact congrArg Fin.castSucc (hα (Fin.castSucc_inj.mp he))

/-- 元の始点零を保つ順序写像の終点固定延長も、始点零を保つ。 -/
lemma roofPointExtend_zero {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) (h₀ : α.toOrderHom 0 = 0) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α).toOrderHom 0 = 0 := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom (0 : Fin (m + 1)).castSucc = 0
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc, h₀]
  rfl

/-- 元の零を避ける順序写像の終点固定延長も、零を避ける。 -/
lemma roofPointExtend_avoids_zero {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (hz : ∀ i, α.toOrderHom i ≠ 0) (j : Fin (m + 2)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α).toOrderHom j ≠ 0 := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom j ≠ 0
  induction j using Fin.lastCases with
  | last => rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last]; simp
  | cast j =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc]
    exact Fin.castSucc_ne_zero_iff.mpr (hz j)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
