module

public import SerrePositivity.InfinityCategories.F1.CylinderBoundaryEndpointConditions

/-!
概要：同値な両端写像を固定した円柱上の実際の区間族の lift 空間は可縮。
方針：境界 fiber、同時端点 fiber、同値な四角形の端点 fiber を厳密な同型で結ぶ。
規約：内部の分類区間も全高次 lift も自由に動かす。
使われ方：Kerodon Lemma 5.6.9.1 の区間側への可縮性の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：実際の同値な関手を同値の関手空間の頂点として表す。
方針：関手の頂点に同値条件を添える。
規約：逆関手の選択は頂点のデータに含めない。
使われ方：指定した両端同値の fiber を実際の写像で表す。 -/
def pointedPrismSourceEquivalenceVertex {K : SSet.{u + 1}} [Quasicategory K]
    {s : SpaceInfinity.{u} _⦋0⦌} (g : K ⟶ vertexFiber pointedSpaceProjection s)
    (hg : IsQCatEquivalence g) : (pointedPrismSourceEquivalenceSpace K s) _⦋0⦌ :=
  ⟨functorVertex g, by
    intro v
    obtain rfl : v = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    simp only [op_id, Functor.map_id_apply]
    exact hg⟩

/-- 概要：指定した同値の頂点を包含すると元の関手頂点。
方針：全部分複体の包含の定義。
規約：厳密な頂点の一致。
使われ方：両端制限の fiber の同定。 -/
lemma pointedPrismSourceEquivalenceVertex_ι {K : SSet.{u + 1}} [Quasicategory K]
    {s : SpaceInfinity.{u} _⦋0⦌} (g : K ⟶ vertexFiber pointedSpaceProjection s)
    (hg : IsQCatEquivalence g) :
    (pointedPrismSourceEquivalenceι K s).app _ (pointedPrismSourceEquivalenceVertex g hg) =
      functorVertex g := rfl

/-- 概要：同値な二つの端点写像を固定した全四角形の同時端点 fiber は可縮。
方針：同値な四角形の両端制限の trivial Kan fibration の fiber を引き戻し同型で移す。
規約：円柱の貼り付け射 f に同値性は要求しない。
使われ方：実際の境界固定 lift の可縮性の入力。 -/
lemma cylinderFixedEndpointFiber_isContractibleKan {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J)
    {s t : SpaceInfinity.{u} _⦋0⦌}
    (g₀ : K ⟶ vertexFiber pointedSpaceProjection s) (h₀ : IsQCatEquivalence g₀)
    (g₁ : J ⟶ vertexFiber pointedSpaceProjection t) (h₁ : IsQCatEquivalence g₁) :
    IsContractibleKan (vertexFiber (lift (cylinderFixedEndpointSquareSource f s t)
      (cylinderFixedEndpointSquareTarget f s t)) (functorVertex g₀, functorVertex g₁)) := by
  have := cylinderEquivalenceSquareEndpoints_trivialKanFibration f s t
  let b := (pointedPrismSourceEquivalenceVertex g₀ h₀, pointedPrismSourceEquivalenceVertex g₁ h₁)
  have hc := vertexFiber_isContractibleKan (cylinderEquivalenceSquareEndpoints f s t) b
  exact isContractibleKan_of_iso
    (vertexFiberPullbackIso
      (lift (cylinderFixedEndpointSquareSource f s t) (cylinderFixedEndpointSquareTarget f s t))
      (pointedPrismSourceEquivalenceι K s ⊗ₘ pointedPrismSourceEquivalenceι J t) b) hc

/-- 概要：同値な両端写像を固定し内部の分類区間全体を動かす実際の円柱 lift 空間は可縮。
方針：二つの厳密な fiber 同型で同時端点制限の可縮性を移す。
規約：固定した一つの分類区間の lift だけでなく区間族全体の可縮性。
使われ方：区間上の表現空間の境界 fiber の可縮性へ渡す円柱側の結論。 -/
lemma cylinderFixedBoundaryFamilySpace_isContractibleKan {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J)
    {s t : SpaceInfinity.{u} _⦋0⦌}
    (g₀ : K ⟶ vertexFiber pointedSpaceProjection s) (h₀ : IsQCatEquivalence g₀)
    (g₁ : J ⟶ vertexFiber pointedSpaceProjection t) (h₁ : IsQCatEquivalence g₁) :
    IsContractibleKan (cylinderFixedBoundaryFamilySpace f g₀ g₁) := by
  have hc := cylinderFixedEndpointFiber_isContractibleKan f g₀ h₀ g₁ h₁
  have hb := isContractibleKan_of_iso (cylinderBoundaryEndpointFiberIso f g₀ g₁).symm hc
  exact isContractibleKan_of_iso (cylinderFixedBoundaryFamilyFiberIso f g₀ g₁).symm hb

end SerrePositivity.InfinityCategories
