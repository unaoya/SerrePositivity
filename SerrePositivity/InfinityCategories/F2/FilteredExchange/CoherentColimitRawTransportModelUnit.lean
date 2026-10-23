module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitRawTransportModelIso
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitRawFirstUnitModel

/-!
概要：raw 輸送模型比較を、元の余錐 fiber 写像と単位比較で元の模型単位両端へ戻す。
方針：元の余錐単位比較の実始点と、同じ Kan 頂点射の単位自然性を用いる。
規約：選択済み比較と元の単位を保持。使われ方：第一辺合成輸送を模型比較で照合する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (a : SSet.Homotopy F G)
local notation "f" => coherentTransformationTotalMap F G (coherentVertexOfHomotopy a)
local notation "m" => CategoryTheory.Functor.map SSet.uliftFunctor (coherentTotalVertexMap F G f)
local notation "c" => coconeFiberMap (coherentDiagramTotalCocone F)
local notation "VF" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex F)
local notation "VG" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex G)
local notation "M" => Iso.inv (smallLeftUnstraighteningIso F) ≫
  CategoryTheory.Functor.map SSet.uliftFunctor (f ≫ coherentDiagramTotalUnit G)

/-- 元の単位比較の実始点は、同じ余錐 fiber 写像・固定値射・具体的 Kan 頂点射の合成。 -/
lemma coherentColimitRawTransportModelUnit_source :
    (coconeFiberValueMapAt (coherentDiagramTotalCocone F) (coherentDiagramTotalVertex F)
      (coherentDiagramTotalCocone_vertex F)) ≫ m = c ≫ (VF ≫ m) := by
  rw [coconeFiberValueMapAt_eq_valueTo, Category.assoc]

/-- 元の余錐単位比較を、元の raw 模型比較の実終点から元の模型単位終点へ写す。 -/
def coherentColimitRawTransportModelUnitFactor : FunctorIso (c ≫ (VF ≫ m)) M :=
  functorIsoOfEq ((coherentLargeTotalCoconeUnitIso F).postcomp m)
    (coherentColimitRawTransportModelUnit_source B a)
    (coherentColimitNativeAction_unit_lift B a)

/-- 元の raw 輸送模型比較を単位で前合成し、同じ余錐単位比較で元の模型単位両端へ戻す。 -/
def coherentColimitRawTransportModelUnitComparison :
    FunctorIso (c ≫ coherentColimitFiberTransport B a ≫
      (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex G)).hom) M :=
  functorIsoOfEq
    ((coherentColimitRawTransportModelIso B a).precomp c ≪≫
      coherentColimitRawTransportModelUnitFactor B a)
    (congrArg (fun r => c ≫ r) (coherentColimitRawFiberTransport_valueTo B a)) rfl

end SerrePositivity.InfinityCategories.F2
