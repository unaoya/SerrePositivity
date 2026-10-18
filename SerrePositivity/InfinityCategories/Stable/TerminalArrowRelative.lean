module
public import SerrePositivity.InfinityCategories.Stable.TerminalPrismLast
public import SerrePositivity.InfinityCategories.Core.RelativeTerminalExtension
public import SerrePositivity.InfinityCategories.Core.EquivalencePath

/-! # 終対象へ向かう辺の相対終点境界充填

概要：辺の終点が終対象なら、始点評価に関してその辺は相対終点境界を充填する。
方針：境界の辺の族を uncurry し、最後の終点だけを使う prism 延長を適用する。
規約：他の境界の辺の終点は自由に動く。
使われ方：S4 の終対象へ向かう span の比較の一意性。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：終対象を終点とする辺は始点評価の相対終点境界を充填する。
方針：指定した始点の族を保って prism を延長し、curry で辺の族へ戻す。
規約：値域の quasicategory 性は不要。使われ方：span の二辺への相対延長。 -/
lemma terminalBoundaryLifting_arrowSource_of_terminalTarget {X : SSet.{u}}
    (g : (Δ[1] : SSet.{u}) ⟶ X)
    (hg : IsTerminalVertex (g.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) :
    TerminalBoundaryLifting (evaluateFunctorAt (Y := X)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (functorVertex g) := by
  intro n a b hb sq
  let H := uncurry a
  have h₀ : (boundary (n + 1)).ι ≫ b =
      prismEndpoint 0 (boundary (n + 1) : SSet.{u}) ≫ H := by
    rw [← curry_evaluateFunctorAt_interval, curry_uncurry]
    exact sq.w.symm
  have hlast : a.app (Opposite.op ⦋0⦌)
      ⟨stdSimplex.obj₀Equiv.symm (Fin.last (n + 1)), vertex_mem_boundary n _⟩ =
        functorVertex g := by
    apply SSet.yonedaEquiv.symm.injective
    simpa only [boundaryVertex, SSet.yonedaEquiv_symm_comp] using hb
  have ht : IsTerminalVertex (H.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2),
        ⟨stdSimplex.obj₀Equiv.symm (Fin.last (n + 1)), vertex_mem_boundary n _⟩)) := by
    change IsTerminalVertex ((a.app (Opposite.op ⦋0⦌)
      ⟨stdSimplex.obj₀Equiv.symm (Fin.last (n + 1)), vertex_mem_boundary n _⟩).app
        (Opposite.op ⦋0⦌) (𝟙 _) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    rw [hlast]
    exact hg
  obtain ⟨F, hF, hF₀⟩ := stable_prism_extend_terminal_last n H b h₀ ht
  refine ⟨curry F, ?_, ?_⟩
  · apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry]
    exact hF
  · rw [curry_evaluateFunctorAt_interval, hF₀]

end SerrePositivity.InfinityCategories
