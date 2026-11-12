module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopEquivalenceZeroTriangle
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopEquivalenceCofiberExists
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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：指定した元の loop 同値から安定性を導く。
方針：零対象と全辺の fiber/cofiber、零角の双方向判定をまとめる。
規約：切断の終点等号と実 loop 関手の同値性を明示する。
使われ方：HA Corollary 1.4.2.27 の一般 loop 判定。 -/
theorem isStable_of_loopEquivalence {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X]
    (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X where
  toHasZeroVertex := inferInstance
  fiber_exists f := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_fiberSquare_of_cospan_limits
    (fun p ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits.hasLimit p) f
  cofiber_exists f := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSquare_nonempty_of_loopEquivalence s hs hΩ f
  fiber_iff_cofiber t := t.isFiber_iff_isCofiber_of_loopEquivalence s hs hΩ

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
