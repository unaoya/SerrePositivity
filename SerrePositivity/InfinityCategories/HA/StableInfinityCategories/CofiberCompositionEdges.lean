module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberLocalizingComposition

/-! # 端点付き合成二単体の Verdier 分母

概要：実合成構造を入力に、端点付き三辺の分母の二対三性を公開する。
方針：合成構造の三面を元の辺と厳密に照合する。
規約：辺の選択を変更しない。使われ方：共通分母の全細分辺の所属。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]

/-- 端点付き実合成構造の三辺に対する二対三性。 -/
theorem cofiberStableEdges_compStruct_twoOfThree (P : Set (X _⦋0⦌))
    {x y z : X _⦋0⦌}
    {f : Truncated.Edge (X := (truncation 2).obj X) x y}
    {g : Truncated.Edge (X := (truncation 2).obj X) y z}
    {h : Truncated.Edge (X := (truncation 2).obj X) x z}
    (c : Truncated.Edge.CompStruct f g h) :
    let W := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges {a | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P a}
    (f.edge ∈ W → g.edge ∈ W → h.edge ∈ W) ∧
      (f.edge ∈ W → h.edge ∈ W → g.edge ∈ W) ∧
      (g.edge ∈ W → h.edge ∈ W → f.edge ∈ W) := by
  have hf : SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫
      SSet.yonedaEquiv.symm c.simplex) = f.edge := by
    rw [stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv.apply_symm_apply]
    exact c.d₂
  have hg : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫
      SSet.yonedaEquiv.symm c.simplex) = g.edge := by
    rw [stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv.apply_symm_apply]
    exact c.d₀
  have hh : SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫
      SSet.yonedaEquiv.symm c.simplex) = h.edge := by
    rw [stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv.apply_symm_apply]
    exact c.d₁
  have ht := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_twoOfThree P (SSet.yonedaEquiv.symm c.simplex)
  dsimp only at ht ⊢
  rwa [hf, hg, hh] at ht

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
