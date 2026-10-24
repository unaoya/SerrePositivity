module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.InitialShapeLimitExchange
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentFilteredLimitExchange
public import SerrePositivity.InfinityCategories.Core.UniverseSSetMaps

/-!
概要：全ての標準単体について、元の coherent filtered 余極限は極限錐を保つ。
方針：宇宙を上げた単体の最初の頂点の包含を同型で表示し、指定脚の判定を使う。
規約：元の錐・余錐を保持。使われ方：有限セル帰納の単体条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 標準単体形状では、元の点ごとの coherent filtered 余極限は極限錐を保つ。 -/
lemma coherentFilteredLimitExchangeShape_simplex (n : ℕ) :
    CoherentFilteredLimitExchangeShape (Δ[n] : SSet.{u}) := by
  intro B hB hfil p c hc hp
  let f : (Δ[0] : SSet.{u + 1}) ⟶ Δ[n] :=
    SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))
  have : Mono f := stdSimplex_firstVertex_mono n
  let a := f ≫ (HomotopyLimits.uliftStdSimplexIso.{u, u + 1} n).inv
  have : Mono a := by dsimp only [a]; infer_instance
  have ha : leftAnodyneExtensions a :=
    leftAnodyneExtensions.comp_mem f _ (stdSimplex_firstVertex_leftAnodyne n)
      (MorphismProperty.of_isIso leftAnodyneExtensions _)
  apply pointwiseColimit_preserves_initialShapeLimits a ha c hc
  rintro ⟨b⟩
  exact hp b

end SerrePositivity.InfinityCategories.F2
