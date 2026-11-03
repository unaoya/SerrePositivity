module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierOverLimitCone
public import SerrePositivity.InfinityCategories.F1B.FunctorIsoConstantEdges
public import SerrePositivity.InfinityCategories.Core.CatInfinity.NativeConeLeg
/-!
概要：任意反転関手の実分母図式の任意の実極限錐は、同じ各脚が全て可逆。
方針：指定頂点の実評価極限錐との全錐同型と、定値全錐への比較 prism を合成する。
規約：極限対象の同型だけで脚の可逆性を推論しない。使われ方：右 Kan 単位の実成分の可逆性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
/-- 実分母図式の任意の実極限錐を、元の対象の像の定値全錐と全関手圏で同定する。 -/
def dgVerdierOverLimitConeFunctorIso (P : Set D) (x : D)
    {Y : SSet.{max u v}} [Quasicategory Y] (F : dgNerve A D ⟶ Y)
    (hF : InvertsEdges F (dgVerdierEdges A D P))
    (c : JoinCone (dgVerdierOverSource A D P x ≫ F)) (hc : IsLimitCone c) :
    FunctorIso c.val (SSet.const (F.app (Opposite.op ⦋0⦌) (Simplex.vertex x))) := by
  let t := dgVerdierOverLimitConeTransport A D P x F hF
  exact coneFunctorIsoOfVertexIso c t.cone (limitConeIso c t.cone hc t.isLimit) ≪≫
    functorIsoOfPointwiseInvertibleHomotopy t.homotopy t.vertical_isInvertible
/-- 同じ実分母図式の任意の極限錐の、指定実分母への同じ脚が可逆。 -/
lemma dgVerdierOverLimitCone_leg_isInvertible (P : Set D) (x : D)
    {Y : SSet.{max u v}} [Quasicategory Y] (F : dgNerve A D ⟶ Y)
    (hF : InvertsEdges F (dgVerdierEdges A D P))
    (c : JoinCone (dgVerdierOverSource A D P x ≫ F)) (hc : IsLimitCone c)
    (i : (dgVerdierOver A D P x : SSet) _⦋0⦌) : IsInvertibleEdge (F2.nativeConeLeg c i) := by
  have h := functorIso_const_map_isInvertible _
    (dgVerdierOverLimitConeFunctorIso A D P x F hF c hc) (F2.coneDomainLeg i)
  exact (isInvertibleEdge_congr (e := F2.nativeConeLeg c i)
    (f := (F2.coneDomainLeg i).map ((truncation 2).map c.val)) rfl).mpr h
end SerrePositivity.InfinityCategories
