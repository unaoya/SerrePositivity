module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.OneConeSimplexShape

/-!
概要：二表示の全比較の偶数・奇数の前置面を、二回の一頂点延長に接続する。
方針：標準単体への全射を頂点で検出し、元の各挿入位置を計算する。
規約：全形状の次元は 2n+1。使われ方：両側の全添字図式と全比較の部分列の一致。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 左側の全前置図式は全比較の偶数番目の頂点を通る。 -/
def comparisonEvenFace (n : ℕ) : (Δ[n] : SSet.{u}) ⟶ Δ[2 * n + 1] :=
  SSet.stdSimplex.map (SimplexCategory.Hom.mk
    { toFun := fun i : Fin (n + 1) ↦ (⟨2 * i.val, by omega⟩ : Fin (2 * n + 1 + 1))
      monotone' := fun _ _ h ↦ Nat.mul_le_mul_left 2 h })

/-- 右側の全前置図式は全比較の奇数番目の頂点を通る。 -/
def comparisonOddFace (n : ℕ) : (Δ[n] : SSet.{u}) ⟶ Δ[2 * n + 1] :=
  SSet.stdSimplex.map (SimplexCategory.Hom.mk
    { toFun := fun i : Fin (n + 1) ↦ (⟨2 * i.val + 1, by omega⟩ : Fin (2 * n + 1 + 1))
      monotone' := fun _ _ h ↦ Nat.add_le_add_right (Nat.mul_le_mul_left 2 h) 1 })

/-- 左側の次の前置面は、左因子を一頂点延ばして全比較の最後の頂点を除いたもの。 -/
lemma comparisonEvenFace_succ_join (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ comparisonEvenFace.{u} (n + 1) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (comparisonEvenFace n) (𝟙 Δ[0]) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join Δ[2 * n + 1] Δ[0]) Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.doubleConeSimplexIso (2 * n + 1)).hom := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  rintro ⟨i, x, y⟩
  fin_cases i
  · cases x
    have hy : y = SSet.stdSimplex.obj₀Equiv.symm 0 := by
      apply SSet.stdSimplex.obj₀Equiv.injective
      simpa only [Equiv.apply_symm_apply] using Fin.eq_zero (SSet.stdSimplex.obj₀Equiv y)
    subst y
    apply SSet.stdSimplex.obj₀Equiv.injective
    apply Fin.ext
    rfl
  · cases y
    apply SSet.stdSimplex.obj₀Equiv.injective
    apply Fin.ext
    rfl

/-- 右側の次の前置面は、旧右面を全比較に残して最後の新頂点を加えたもの。 -/
lemma comparisonOddFace_succ_join (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ comparisonOddFace.{u} (n + 1) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (comparisonOddFace n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[2 * n + 1] Δ[0]) (𝟙 Δ[0]) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.doubleConeSimplexIso (2 * n + 1)).hom := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  rintro ⟨i, x, y⟩
  fin_cases i
  · cases x
    have hy : y = SSet.stdSimplex.obj₀Equiv.symm 0 := by
      apply SSet.stdSimplex.obj₀Equiv.injective
      simpa only [Equiv.apply_symm_apply] using Fin.eq_zero (SSet.stdSimplex.obj₀Equiv y)
    subst y
    apply SSet.stdSimplex.obj₀Equiv.injective
    apply Fin.ext
    rfl
  · cases y
    apply SSet.stdSimplex.obj₀Equiv.injective
    apply Fin.ext
    rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
