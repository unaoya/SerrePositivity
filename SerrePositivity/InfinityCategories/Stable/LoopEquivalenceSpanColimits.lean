module
public import SerrePositivity.InfinityCategories.Stable.LoopEquivalenceCofiberExists
public import SerrePositivity.InfinityCategories.Stable.SpecifiedCofiberSpan

/-!
概要：実 loop 同値から指定した零枝を持つ全 span の余極限を得る。
方針：構成済みの全 cofiber の span と、元の入力 span を全関手同型で比較する。
規約：有限余極限や一般安定性は入力しない。
使われ方：関手圏の cofiber 四角形の点ごとの評価。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：第二枝が指定終対象へ向かう元の span は余極限を持つ。
方針：第一枝の実 cofiber を選び、同じ第一枝と終対象への第二枝を比較する。
規約：第二枝を任意の零射へ置き換えない。
使われ方：全パラメーターの評価における cofiber の存在。 -/
lemma hasColimit_span_of_terminal_second_of_loopEquivalence {X : SSet.{u}}
    [Quasicategory X] [HasZeroVertex X] [HasFiniteLimits X]
    (s : X ⟶ loopDiagrams X) (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0))
    (p : (horn 2 0 : SSet.{u}) ⟶ X)
    (hz : IsTerminalVertex ((horn₂₀.ι₀₂ ≫ p).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) : HasColimit p := by
  let e := edgeOfSimplex (SSet.yonedaEquiv (horn₂₀.ι₀₁ ≫ p))
  obtain ⟨t⟩ := cofiberSquare_nonempty_of_loopEquivalence s hs hΩ e
  have hfirst : horn₂₀.ι₀₁ ≫ p = horn₂₀.ι₀₁ ≫ pushoutSpan t.square := by
    rw [pushoutSpan, ← Category.assoc, spanSquareBoundary_bottomEdge, t.bottom_edge]
    exact (SSet.yonedaEquiv.symm_apply_apply _).symm
  have ht : IsTerminalVertex ((horn₂₀.ι₀₂ ≫ pushoutSpan t.square).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
    rw [pushoutSpan, ← Category.assoc, spanSquareBoundary_leftEdge]
    exact t.zero_corner.2
  obtain ⟨i⟩ := nonempty_functorIso_span_of_first_eq_terminal_second
    p (pushoutSpan t.square) hfirst hz ht
  exact (hasColimit_iff_of_functorIso i).mpr ⟨pushoutCocone t.square, t.isPushout⟩

end SerrePositivity.InfinityCategories
