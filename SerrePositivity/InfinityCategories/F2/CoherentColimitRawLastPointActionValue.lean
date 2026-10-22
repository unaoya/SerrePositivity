module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitRawLastLongCancellation
public import SerrePositivity.InfinityCategories.F2.FunctorIsoPrecompPostcompTransport

/-!
概要：元の最後辺の raw 指定比較の単位と固定値への像を、元の一点比較の同じ像へ戻す。
方針：元の実両端の表示変更を除き、二段の前合成と固定値への後合成を交換する。
規約：元の二比較と実下側作用を保持。使われ方：模型三角形式の残余因子の消去。
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
  (a : SSet.Homotopy F G) (b : SSet.Homotopy G J)
local notation "ma" => Subtype.val (leftUnstraighteningMappingVertexMap _ _
  (coherentVertexOfHomotopy (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B a))))
local notation "u₀" => Subtype.val (leftUnstraighteningMappingVertexMap F
  (SSet.const (JoinCocone.vertex (coherentDiagramTotalCocone F)))
  (coconeTransformationVertex (coherentDiagramTotalCocone F)))
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex J)

/-- 元の指定 raw 比較の単位・値への像は、元の下側実作用で制限した同じ一点比較。 -/
lemma coherentColimitRawLastPointAction_value_heq_point :
    HEq (((coherentColimitRawLastPointActionIso B a b).precomp u₀).postcomp V)
      ((coherentColimitConstantPointValueToIso B b).precomp
        (coherentColimitRawLowerCompositeAction B a)) := by
  have hr := functorIso_postcomp_heq_of_heq
    (coherentColimitConstantTransportPointIso B b) (coherentColimitConstantTransportRawPointIso B b)
    rfl (coherentColimitConstantTransport_raw_point_target B b)
    (coherentColimitConstantTransportRawPointIso_heq_point B b) V
  have hv : HEq ((coherentColimitConstantTransportRawPointIso B b).postcomp V)
      (coherentColimitConstantPointValueToIso B b) :=
    hr.trans (functorIsoOfEq_heq _ _ _).symm
  have hmap : u₀ ≫ ma = coherentColimitRawLowerCompositeAction B a := by
    unfold coherentColimitRawLowerCompositeAction
    rw [coherentVertexOfHomotopy_cocone]
  have hh := functorIso_precomp_precomp_postcomp_heq
    (coherentColimitConstantTransportRawPointIso B b) (coherentColimitConstantPointValueToIso B b)
    ma u₀ (coherentColimitRawLowerCompositeAction B a) V (Category.assoc _ _ _).symm
    (congrArg (fun f => f ≫ V) (coherentColimitConstantTransport_raw_point_target B b)) hv hmap
  exact (functorIsoOfEq_precomp_postcomp_heq
    ((coherentColimitConstantTransportRawPointIso B b).precomp ma)
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm u₀ V).trans hh

end SerrePositivity.InfinityCategories.F2
