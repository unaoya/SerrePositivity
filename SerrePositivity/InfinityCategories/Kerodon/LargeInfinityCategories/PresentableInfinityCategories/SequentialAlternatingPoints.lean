module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AlternatingInsertedVertices
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialDiagramFiniteStages

/-!
概要：交互次段の挿入点を可算 nerve の元の奇数頂点に同定する。
方針：標準単体の頂点値を計算し、有限始区間の全射を合成する。
規約：標準単体を標的とする頂点検出と Yoneda の全単射だけを使う。
使われ方：全交互可算図式の奇数部分列の全関手比較。

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

private lemma eqToHom_vertex_value {m n : ℕ} (h : m = n)
    (x : (Δ[m] : SSet.{u}) _⦋0⦌) :
    (SSet.stdSimplex.obj₀Equiv ((eqToHom (congrArg
      (fun k ↦ (Δ[k] : SSet.{u})) h)).app _ x)).val = (SSet.stdSimplex.obj₀Equiv x).val := by
  cases h
  rfl

/-- 概要：挿入点の標準頂点番号は元の奇数 2n+1。
方針：右 join の最初の頂点の値を計算する。
規約：元の標準単体の実頂点の等式。
使われ方：可算 nerve の奇数頂点との比較。 -/
lemma alternatingInsertedPoint_vertex (n : ℕ) :
    SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingInsertedPoint.{u} n) =
      SSet.stdSimplex.obj₀Equiv.symm (⟨2 * n + 1, by omega⟩ : Fin (2 * (n + 1) + 1)) := by
  apply SSet.stdSimplex.obj₀Equiv.injective
  apply Fin.ext
  change (SSet.stdSimplex.obj₀Equiv ((eqToHom (congrArg (fun k ↦ (Δ[k] : SSet.{u}))
    (by omega : 2 * n + 1 + 1 = 2 * (n + 1)))).app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (2 * n) 1).hom.app _
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[2 * n] Δ[1]).app _
          ((SSet.stdSimplex.δ (1 : Fin 2)).app _ (SSet.yonedaEquiv (𝟙 Δ[0]))))))).val = _
  rw [eqToHom_vertex_value (by omega : 2 * n + 1 + 1 = 2 * (n + 1))]
  rfl

/-- 概要：挿入点を全可算 nerve へ送ると元の奇数頂点の点射になる。
方針：Yoneda 座標で有限始区間の値を計算する。
規約：点からの全射の厳密な等式。
使われ方：全有限段比較を奇数部分列の頂点へ適用する。 -/
lemma alternatingInsertedPoint_initialSimplex (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingInsertedPoint.{u} n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex (2 * (n + 1)) =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up (2 * n + 1) : ULift.{u} ℕ)) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, alternatingInsertedPoint_vertex, Equiv.apply_symm_apply]
  exact ComposableArrows.ext (fun i ↦ by
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl) (fun _ _ ↦ Subsingleton.elim _ _)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
