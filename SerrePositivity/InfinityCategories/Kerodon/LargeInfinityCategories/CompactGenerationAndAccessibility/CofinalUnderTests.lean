module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallQuasicategoryDiagramFactorization
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.LiftedPointQuillenA
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.LiftedShapeFilteredCriterion
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredWeakContractibility

/-!
概要：指定始点の下の小さい quasicategory 試験余錐から cofinal 性を得る。
方針：有界な全試験因子化、filtered 弱可縮性、既存の Quillen A を合成する。
規約：元の全射と元の under comma を保持する。
使われ方：一般 accessible 引き戻しの compact 成分射影。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：指定始点の下の各小さい quasicategory 図式が余錐を持てば元の射は right cofinal。
方針：元の under comma の任意の小試験に戻し、filtered 判定と Quillen A を使う。
規約：頂点の被覆だけで cofinal 性を主張しない。
使われ方：全追加入力を保持する交互構成から成分密度を回収する。 -/
lemma isRightCofinal_of_quasicategory_under_tests
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {X Y : SSet.{u + 1}} [Quasicategory X] [Quasicategory Y] (F : X ⟶ Y)
    (hTest : ∀ z : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[0] : SSet.{u}) ⟶ Y,
      ∀ (K : SSet.{u}) (hK : Quasicategory K), letI := hK
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ K → ∀ r : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶
          pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z) F, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal F := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isRightCofinal_of_weaklyContractible_lifted_point_under
  intro z
  have hfiltered := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isFilteredInfinity_of_liftedShape_cocones (Fact.out : μ.IsRegular)
    (pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z) F) (fun hK r ↦
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nonempty_cocone_of_smallQuasicategory_tests hμ
        (fun K hQ hsmall r ↦ hTest z K hQ hsmall r) _ hK r)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isWeaklyContractible_of_isFilteredInfinity _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
