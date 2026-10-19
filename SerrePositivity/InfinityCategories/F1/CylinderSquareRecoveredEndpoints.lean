module

public import SerrePositivity.InfinityCategories.F1.CylinderSquarePrismRecovery

/-!
概要：四角形から戻した全 prism lift の二端点の回収。
方針：普遍 prism の制限を内部 Hom の前合成として計算する。
規約：貼り付け射で前合成した終点の族まで厳密に保つ。
使われ方：両端同値を課した引き戻しへの逆比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：全 prism lift の終点を含めると普遍 prism の終点への制限。
方針：評価の終点公式を curry する。
規約：全高次パラメーターでの射の等式。
使われ方：四角形から戻した lift の終点の回収。 -/
lemma pointedPrismLiftEndpoint_ι (K : SSet.{u + 1}) (s t : SpaceInfinity.{u} _⦋0⦌) :
    pointedPrismLiftEndpoint K s t ≫ (ihom K).map (vertexFiberι pointedSpaceProjection t) =
      prismLiftSpaceCurry pointedSpaceProjection K (pointedPrismData K s t) ≫
        (pre (prismEndpoint 1 K)).app _ := by
  apply uncurry_injective
  rw [uncurry_natural_right, uncurry_pre_app]
  exact (pointedPrismEvaluation_one K s t).symm

/-- 概要：四角形から戻した lift の始点は元の四角形の始点写像。
方針：パラメーターの回収式の第一成分を取る。
規約：厳密な射の等式。
使われ方：始点同値への制限の可換性。 -/
lemma cylinderFixedEndpointSquareLift_source {K J : SSet.{u + 1}} (f : K ⟶ J)
    (s t : SpaceInfinity.{u} _⦋0⦌) :
    cylinderFixedEndpointSquareLift f s t ≫ pointedPrismLiftSource K s t =
      cylinderFixedEndpointSquareSource f s t := by
  change (cylinderFixedEndpointSquareLift f s t ≫ pointedPrismLiftParameters K s t) ≫ fst _ _ = _
  rw [cylinderFixedEndpointSquareLift_parameters, lift_fst]

/-- 概要：四角形から戻した lift の終点は元の終点写像を貼り付け射で前合成したもの。
方針：円柱の終点の貼り合わせ条件と内部 Hom の自然性を使う。
規約：包含後だけでなく fiber 値の写像自体の厳密な等式。
使われ方：円柱の両端同値を持つ中間空間への逆比較の条件。 -/
lemma cylinderFixedEndpointSquareLift_endpoint {K J : SSet.{u + 1}} (f : K ⟶ J)
    (s t : SpaceInfinity.{u} _⦋0⦌) :
    cylinderFixedEndpointSquareLift f s t ≫ pointedPrismLiftEndpoint K s t =
      cylinderFixedEndpointSquareTarget f s t ≫ (pre f).app _ := by
  have h : (cylinderFixedEndpointSquareLift f s t ≫ pointedPrismLiftEndpoint K s t) ≫
        (ihom K).map (vertexFiberι pointedSpaceProjection t) =
      (cylinderFixedEndpointSquareTarget f s t ≫ (pre f).app _) ≫
        (ihom K).map (vertexFiberι pointedSpaceProjection t) := by
    calc
      _ = cylinderFixedEndpointSquarePointed f s t ≫
          (pre (pushout.inl (prismEndpoint 1 K) f)).app _ ≫ (pre (prismEndpoint 1 K)).app _ := by
        rw [Category.assoc, pointedPrismLiftEndpoint_ι, ← Category.assoc,
          cylinderFixedEndpointSquareLift_curry, Category.assoc]
      _ = cylinderFixedEndpointSquarePointed f s t ≫
          (pre (prismEndpoint 1 K ≫ pushout.inl (prismEndpoint 1 K) f)).app _ := by
        rw [← NatTrans.comp_app, ← pre_map]
      _ = cylinderFixedEndpointSquarePointed f s t ≫
          (pre (f ≫ pushout.inr (prismEndpoint 1 K) f)).app _ := by rw [pushout.condition]
      _ = (cylinderFixedEndpointSquareTarget f s t ≫
          (ihom J).map (vertexFiberι pointedSpaceProjection t)) ≫ (pre f).app _ := by
        rw [cylinderFixedEndpointSquareTarget_ι, pre_map, NatTrans.comp_app, Category.assoc]
      _ = _ := by rw [Category.assoc, (pre f).naturality, Category.assoc]
  apply uncurry_injective
  apply vertexFiber_hom_ext pointedSpaceProjection t
  simpa only [uncurry_natural_right] using congrArg uncurry h

end SerrePositivity.InfinityCategories
