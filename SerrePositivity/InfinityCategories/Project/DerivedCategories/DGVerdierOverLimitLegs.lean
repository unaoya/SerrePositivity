module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierOverLimitCone
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorIsoConstantEdges
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.NativeConeLeg
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
/-- 実分母図式の任意の実極限錐を、元の対象の像の定値全錐と全関手圏で同定する。 -/
def dgVerdierOverLimitConeFunctorIso (P : Set D) (x : D)
    {Y : SSet.{max u v}} [Quasicategory Y] (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P))
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x ≫ F)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso c.val (SSet.const (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))) := by
  let t := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverLimitConeTransport A D P x F hF
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneFunctorIsoOfVertexIso c t.cone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeIso c t.cone hc t.isLimit) ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy t.homotopy t.vertical_isInvertible
/-- 同じ実分母図式の任意の極限錐の、指定実分母への同じ脚が可逆。 -/
lemma dgVerdierOverLimitCone_leg_isInvertible (P : Set D) (x : D)
    {Y : SSet.{max u v}} [Quasicategory Y] (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P))
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x ≫ F)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c)
    (i : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c i) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.functorIso_const_map_isInvertible _
    (dgVerdierOverLimitConeFunctorIso A D P x F hF c hc) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneDomainLeg i)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c i)
    (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneDomainLeg i).map ((truncation 2).map c.val)) rfl).mpr h
end SerrePositivity.InfinityCategories.Project.DerivedCategories
