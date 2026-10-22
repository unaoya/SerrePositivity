module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitRawUnitFiberTransportEndpoints
public import SerrePositivity.InfinityCategories.F2.CoherentColimitIntervalModelOuterCancellation

/-!
概要：元の模型三角形式の残りを、同じ raw fiber 二面比較と元の最後辺輸送で表す。
方針：同じ二実端点で射影比較を揃え、消去済み模型式へ値の等式を代入する。
規約：三角形・長辺輸送・最後辺模型比較を保持。使われ方：全区間族の三角形整合の反映。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
local notation "P" => coherentColimitRawConstantFiberProjection B G
local notation "A" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B b)
local notation "s" => lift (𝟙 _) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex J)
local notation "g₁" => (s ≫ (P ▷ Δ[0]) ≫
  FiberTransportFamily.endpoint (pointedIntervalTransport A)) ≫ V
local notation "f" => Subtype.val (leftUnstraighteningMappingVertexMap F G
  (coherentVertexOfHomotopy a))

/-- 元の残りの二比較は、同じ一点輸送比較と元の raw fiber 比較の輸送後の値に等しい。 -/
lemma coherentColimitRightTailTransportValueTo_eq_fiber :
    coherentColimitRightTailTransportValueTo B a b =
    (coherentColimitConstantPointValueToIso B b).precomp
      (coherentColimitRawLowerCompositeAction B a) ≪≫
        coherentColimitRawUnitFiberTransportValueTo B a b := by
  have he : functorIsoOfEq ((coherentColimitRawUnitActionComparison B a).postcomp g₁)
      rfl (coherentColimitPointValueTo_upper_target_map B a b) =
      coherentColimitRawUnitFiberTransportValueTo B a b := by
    exact eq_of_heq ((functorIsoOfEq_heq _ _ _).trans
      ((coherentColimitRawUnitAction_transport_heq_fiber B a b).trans
        (functorIsoOfEq_heq _ _ _).symm))
  have h := congrArg (fun k => (coherentColimitConstantPointValueToIso B b).precomp
    (coherentColimitRawLowerCompositeAction B a) ≪≫ k) he
  exact h

/-- 元の a6 模型三角形式の残りは、同じ raw fiber 比較の元の最後辺輸送で回収される。 -/
lemma coherentColimitIntervalModel_fiber_transport [Quasicategory B]
    (T : FunctorCompositionTriangle a b d) :
    coherentColimitIntervalModelUnitComparison B d ≪≫
      vertexIsoOfEq (coherentTotalTriangleNativeModelComparison T)
        (congrArg functorVertex (coherentColimitNativeModelTarget_eq_unit B d))
        (congrArg functorVertex (coherentTotalTriangleNativeModelTarget_eq_unit a b)) =
    coherentColimitIntervalModelTransportRemainder B T ≪≫
      (coherentColimitConstantPointValueToIso B b).precomp
        (coherentColimitRawLowerCompositeAction B a) ≪≫
      coherentColimitRawUnitFiberTransportValueTo B a b ≪≫
        (coherentColimitIntervalModelUnitComparison B b).precomp f := by
  rw [coherentColimitIntervalModel_outer_cancel, coherentColimitRightTailTransportValueTo_eq_fiber]
  simp only [Iso.trans_assoc]

end SerrePositivity.InfinityCategories.F2
