module

public import SerrePositivity.InfinityCategories.F2.PointedIntervalTransport
public import SerrePositivity.InfinityCategories.F1.TransportPrismLiftEquivalence
public import SerrePositivity.InfinityCategories.F1.MappingSpaceModelEquivalence

/-!
概要：元の全左 Hom をパラメータとする pointed-space 輸送の写像空間上の作用は同値。
方針：F1 の普遍輸送の同値性に恒等係数と標準区間比較を入力する。
規約：実際の選択済みの輸送族を扱う。
使われ方：全空間の fiber 写像の前合成から native な余極限性を判定する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：全左 Hom の元の標準区間比較に沿う輸送の作用は圏同値。
方針：区間への curry の往復と、恒等係数による F1 の輸送族の同値性を使う。
規約：元の輸送族を選び直さない。使われ方：全 Hom の前合成との合成の同値性。 -/
lemma pointedHomTransport_isQCatEquivalence (x y : SpaceInfinity.{u}.obj (Opposite.op ⦋0⦌)) :
    IsQCatEquivalence
      (pointedIntervalTransport (pinchedHomLeftToIntervalMappingSpace x y)).map := by
  let a := pinchedHomLeftToIntervalMappingSpace x y
  have hc : intervalMappingCurryOfEndpoints (intervalMappingUncurry a)
      (intervalMappingUncurry_zero a) (intervalMappingUncurry_one a) = a := by
    apply intervalMappingUncurry_injective
    exact intervalMappingUncurry_curryOfEndpoints _ _ _
  apply pointedTransportFamily_map_isQCatEquivalence (𝟙 _)
    (qCatEquivalenceOfIso (Iso.refl _)).isQCatEquivalence
    (intervalMappingUncurry a) (intervalMappingUncurry_zero a) (intervalMappingUncurry_one a)
  rw [hc]
  exact pinchedHomLeftToIntervalMappingSpace_isQCatEquivalence x y

end SerrePositivity.InfinityCategories.F2
