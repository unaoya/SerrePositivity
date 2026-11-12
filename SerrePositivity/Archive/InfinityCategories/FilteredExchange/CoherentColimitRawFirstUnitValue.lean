module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawFirstUnitComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoTransportAlgebra

/-!
概要：元の raw 第一辺合成比較の固定値への像を、元の模型単位比較へ照合する。
方針：三つの実端点と元の二指定比較の値の一致を合成する。
規約：元の第一辺・二面・模型比較を保持。使われ方：長辺分解後の全区間族の照合。
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
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex G)
local notation "u₀" => Subtype.val (leftUnstraighteningMappingVertexMap F
  (SSet.const (JoinCocone.vertex (coherentDiagramTotalCocone F)))
  (coconeTransformationVertex (coherentDiagramTotalCocone F)))

/-- 逆第一辺指定比較の固定値への像は、元の下側輸送因子の同じ逆。 -/
lemma coherentColimitRawFirstUnitInversePoint_value_heq_lower :
    HEq ((coherentColimitRawFirstUnitInversePoint B a).postcomp V)
      (coherentColimitLowerTransportFactorIso B a).symm := by
  have hp := functorIso_postcomp_heq_of_heq
    ((coherentColimitConstantTransportRawPointIso B a).precomp u₀).symm
    (coherentColimitRawFirstUnitInversePoint B a) rfl
    (coherentColimitRawFirstUnit_middle_map B a) (functorIsoOfEq_heq _ _ _) V
  rw [functorIso_postcomp_symm] at hp
  have hs := vertexIso_symm_heq_of_heq _ _
    (coherentColimitRawFirstUnit_middle_value_vertex B a)
    (coherentColimitRawFirstUnit_source_value_vertex B a)
    (coherentColimitLowerTransportFactorIso_heq_raw_point B a).symm
  exact hp.trans hs

/-- 元の raw 第一辺合成比較の値は、元の下側逆因子と同じ native 二面比較の合成。 -/
lemma coherentColimitRawFirstUnitComparison_value_heq_reduced :
    HEq ((coherentColimitRawFirstUnitComparison B a).postcomp V)
      ((coherentColimitLowerTransportFactorIso B a).symm ≪≫
        coherentColimitNativeTriangleActionComparison B a) := by
  unfold coherentColimitRawFirstUnitComparison
  rw [functorIso_postcomp_trans]
  exact vertexIso_trans_heq_of_heq _ _ _ _
    (coherentColimitRawFirstUnit_source_value_vertex B a)
    (congrArg functorVertex (coherentColimitRawUnitFiberValue_source_map B a))
    (congrArg functorVertex (coherentColimitRawUnitFiberValue_target_map B a))
    (coherentColimitRawFirstUnitInversePoint_value_heq_lower B a)
    (coherentColimitRawUnitFiberComparison_valueTo_heq_native B a)

end SerrePositivity.InfinityCategories.F2
