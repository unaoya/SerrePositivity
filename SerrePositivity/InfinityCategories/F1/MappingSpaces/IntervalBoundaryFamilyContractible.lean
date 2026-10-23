module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.CylinderBoundaryFamilyContractible
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalBoundaryFamilyComparison

/-!
概要：区間上の left fibration の両端同値を固定した全分類族は可縮。
方針：輸送円柱の比較の前合成同値性で円柱側の可縮性を戻す。
規約：分類区間も全高次 lift も自由に動く。
使われ方：区間上の実際の表現空間の境界 fiber の可縮性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：同値な両端写像を固定した区間上の全 lift 族の空間は可縮 Kan 複体。
方針：実際の輸送円柱を選び、境界と射影を厳密に保つ比較で可縮性を反映する。
規約：輸送や分類図式の選択を追加仮定に置かない。
使われ方：Kerodon Lemma 5.6.9.1 の境界 fiber の concrete な模型の可縮性。 -/
lemma intervalFixedBoundaryFamilySpace_isContractibleKan {E : SSet.{u + 1}}
    (p : E ⟶ (Δ[1] : SSet.{u + 1})) [LeftFibration p]
    {s t : SpaceInfinity.{u} _⦋0⦌}
    (g₀ : vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ⟶
      vertexFiber pointedSpaceProjection s) (h₀ : IsQCatEquivalence g₀)
    (g₁ : vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) ⟶
      vertexFiber pointedSpaceProjection t) (h₁ : IsQCatEquivalence g₁) :
    IsContractibleKan (intervalFixedBoundaryFamilySpace p g₀ g₁) := by
  obtain ⟨f, H, hH₁, hH₀, hHp, hc⟩ := exists_intervalTransportCylinder_comparison p
  let c := pushout.desc H (vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) hH₁
  let j := transportCylinderEndpointInclusion f
  let : Mono (j ≫ c) := transportCylinderEndpoint_comparison_mono p f H hH₀ hH₁
  let : Mono j := mono_of_mono j c
  have hi := intervalBoundaryFamily_isContractibleKan_iff p (mappingCylinderIntervalProjection f)
    c hc (intervalFiberEndpointInclusion p) j
    (transportCylinderEndpointInclusion_comparison p f H hH₀ hH₁)
    (intervalTransportCylinder_comparison_projection p f H hH₁ hHp)
    (intervalFiberBoundary_zero p) (intervalFiberBoundary_one p)
    (transportCylinderBoundary_zero f) (transportCylinderBoundary_one f)
    (intervalBoundaryRelativeHom p) (cylinderBoundaryRelativeHom f) g₀ g₁
  exact hi.mpr (cylinderFixedBoundaryFamilySpace_isContractibleKan f g₀ h₀ g₁ h₁)

end SerrePositivity.InfinityCategories
