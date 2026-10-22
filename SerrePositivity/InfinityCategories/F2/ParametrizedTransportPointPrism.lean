module

public import SerrePositivity.InfinityCategories.F2.ParametrizedTransportPullbackFamily
public import SerrePositivity.InfinityCategories.F2.TransportSourcePointPrism

/-!
概要：全普遍輸送の初期値制限の実一点 prism を、同じ実対角普遍 prism へ戻す。
方針：任意の left fibration 上で初期値制限と元の区間族の curry の往復を計算する。
規約：元の輸送を再選択しない。使われ方：pointed 射影での展開を分割した値の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B L K : SSet.{u}} (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
  (c : L ⟶ intervalMappingSpace a b) (l : L _⦋0⦌) (f : K ⟶ vertexFiber p a)
local notation "γ" => intervalMappingUncurry c
local notation "h₀" => intervalMappingUncurry_zero c
local notation "h₁" => intervalMappingUncurry_one c
local notation "U" => parametrizedTransportPullbackFamily p γ h₀ h₁

/-- 元の全区間制限証拠の一点実 prism は、同じ動く初期値と固定区間の実普遍 prism。 -/
lemma parametrizedTransportPullback_point_prism :
    (Δ[1] ◁ lift f (SSet.const l)) ≫ FiberTransportFamily.prism U =
      diagonalUniversalPrism p f (SSet.const (c.app (Opposite.op ⦋0⦌) l)) := by
  rw [parametrizedTransportPullbackFamily_diagonal_prism]
  have hc : intervalMappingCurryOfEndpoints γ h₀ h₁ = c := by
    apply intervalMappingUncurry_injective
    exact intervalMappingUncurry_curryOfEndpoints _ _ _
  rw [hc, SSet.const_comp]

/-- 元の全初期値で制限後の一点実 prism も、同じ元の対角普遍 prism。 -/
lemma parametrizedTransportPullback_source_point_prism :
    (Δ[1] ◁ lift (𝟙 K) (SSet.const l)) ≫ ((U).precomposeSource f).prism =
      diagonalUniversalPrism p f (SSet.const (c.app (Opposite.op ⦋0⦌) l)) := by
  rw [fiberTransportFamily_precomposeSource_point_prism,
    parametrizedTransportPullback_point_prism]

end SerrePositivity.InfinityCategories.F2
