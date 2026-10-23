module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentPrefixTargetMap

/-!
概要：正頂点への標準包含は二正頂点間の区間を全て写す。
方針：零の可能性を除き、後続元の逆像を取る。
規約：ULift した実頂点で全ての順序関係を保持する。
使われ方：prefix 円柱の tail の厳密な計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.F2

/-- 正頂点への標準包含の二点間の全区間には元の区間内の逆像がある。 -/
lemma coherentPositiveVertex_interval (n : ℕ)
    (x y : ULift.{u} (Fin (n + 1))) (z : ULift.{u} (Fin (n + 2)))
    (hx : (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom.uliftMap x ≤ z)
    (hy : z ≤ (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom.uliftMap y) :
    ∃ w : ULift.{u} (Fin (n + 1)), x ≤ w ∧ w ≤ y ∧
      (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom.uliftMap w = z := by
  rcases x with ⟨x⟩
  rcases y with ⟨y⟩
  rcases z with ⟨z⟩
  change x.succ ≤ z at hx
  change z ≤ y.succ at hy
  induction z using Fin.cases with
  | zero => have hx' : x.val + 1 ≤ 0 := hx; omega
  | succ z =>
    exact ⟨ULift.up z, Fin.succ_le_succ_iff.mp hx, Fin.succ_le_succ_iff.mp hy, rfl⟩

end SerrePositivity.InfinityCategories.F2
