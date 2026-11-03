module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RestrictedTransportPrismPresentation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportPointPrismBoundary
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ParametrizedTransportPointPrism
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.IntervalMappingPointUncurry
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalPrismComparisonWitness

/-!
概要：元の全区間の一点直接比較を、同じ実一点 prism の元の対角輸送比較へ戻す。
方針：元の実二 prism の一致から両端も回収し、同じ fiber の指定比較を照合する。
規約：元の初期値・点・実 prism を保持。使われ方：元の長辺の native 値比較への橋渡し。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B K L : SSet.{u}} (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
  (f : K ⟶ vertexFiber p a) (c : L ⟶ intervalMappingSpace a b)
  (W : FiberTransportFamily (b := b) p f (intervalMappingUncurry c)) (l : L _⦋0⦌)
local notation "γ" => intervalMappingUncurry c
local notation "r" => lift (𝟙 K) (SSet.const l)
local notation "v" => (SSet.const (c.app (Opposite.op ⦋0⦌) l) : K ⟶ intervalMappingSpace a b)
local notation "β" => intervalMappingUncurry v
local notation "h₀" => intervalMappingUncurry_zero v
local notation "h₁" => intervalMappingUncurry_one v
local notation "P" => (Δ[1] ◁ r) ≫ FiberTransportFamily.prism W
local notation "U" => parametrizedTransportPullbackFamily p γ
  (intervalMappingUncurry_zero c) (intervalMappingUncurry_one c)

/-- 元の指定一点直接比較は、同じ実一点 prism と全初期値の元の対角比較と値まで一致。 -/
lemma fiberTransportPointComparison_heq_diagonal :
    HEq ((W.endpointIso p f γ (intervalMappingUncurry_one c)
        ((U).precomposeSource f)).precomp r)
      (leftFibrationPrism_diagonalTransportIso p f (r ≫ W.endpoint) β h₀ h₁ P
        (fiberTransportFamily_point_prism_start p f γ W l)
        (fiberTransportFamily_point_prism_finish p f γ W l)
        ((fiberTransportFamily_point_prism_projection p f γ W l).trans
          (intervalMappingPoint_uncurry c l))) := by
  rw [leftFibrationPrism_diagonalTransportIso_eq_witness]
  have hc : intervalMappingCurryOfEndpoints β h₀ h₁ = v := by
    apply intervalMappingUncurry_injective
    exact intervalMappingUncurry_curryOfEndpoints β h₀ h₁
  refine fiberTransportRestrictedPrismComparison_heq_of_prisms p f γ
    (intervalMappingUncurry_one c) W ((U).precomposeSource f) r β
    (f ≫ vertexFiberι p a) ?_ h₁ P
    (diagonalUniversalPrism p f (intervalMappingCurryOfEndpoints β h₀ h₁))
    ((fiberTransportFamily_point_prism_projection p f γ W l).trans
      (intervalMappingPoint_uncurry c l)) ?_
    (fiberTransportFamily_point_prism_start p f γ W l)
    (diagonalUniversalPrism_start p f (intervalMappingCurryOfEndpoints β h₀ h₁))
    (r ≫ W.endpoint) (diagonalFiberTransport p f (intervalMappingCurryOfEndpoints β h₀ h₁))
    (fiberTransportFamily_point_prism_finish p f γ W l)
    (diagonalUniversalPrism_finish p f (intervalMappingCurryOfEndpoints β h₀ h₁))
    ?_ ?_ rfl ?_
  · rw [← whiskerLeft_comp_assoc, lift_snd, intervalMappingPoint_uncurry]
  · simp only [← Category.assoc, lift_fst, Category.id_comp]
  · rw [hc]
    exact parametrizedTransportPullback_source_point_prism p c l f

end SerrePositivity.InfinityCategories.F2
