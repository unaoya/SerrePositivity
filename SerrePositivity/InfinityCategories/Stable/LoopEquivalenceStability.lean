module
public import SerrePositivity.InfinityCategories.Stable.LoopEquivalenceZeroTriangle
public import SerrePositivity.InfinityCategories.Stable.LoopEquivalenceCofiberExists
/-!
概要：実 loop 図式切断と loop 同値から IsStable を結論する。
方針：有限極限による fiber、回転で得た cofiber、任意零角の同値を三条件へ渡す。
規約：有限余極限・ModelCategory・一般安定性を追加仮定にしない。
使われ方：nativeLoop を持つ実スペクトル圏への一般安定性判定。
-/
@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：指定した元の loop 同値から安定性を導く。
方針：零対象と全辺の fiber/cofiber、零角の双方向判定をまとめる。
規約：切断の終点等号と実 loop 関手の同値性を明示する。
使われ方：HA Corollary 1.4.2.27 の一般 loop 判定。 -/
theorem isStable_of_loopEquivalence {X : SSet.{u}}
    [Quasicategory X] [HasZeroVertex X] [HasFiniteLimits X]
    (s : X ⟶ loopDiagrams X) (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0)) : IsStable X where
  toHasZeroVertex := inferInstance
  fiber_exists f := exists_fiberSquare_of_cospan_limits
    (fun p ↦ HasFiniteLimits.hasLimit p) f
  cofiber_exists f := cofiberSquare_nonempty_of_loopEquivalence s hs hΩ f
  fiber_iff_cofiber t := t.isFiber_iff_isCofiber_of_loopEquivalence s hs hΩ

end SerrePositivity.InfinityCategories
