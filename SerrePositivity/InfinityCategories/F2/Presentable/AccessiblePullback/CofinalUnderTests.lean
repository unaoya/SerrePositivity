module

public import SerrePositivity.InfinityCategories.F2.Presentable.SmallQuasicategoryDiagramFactorization
public import SerrePositivity.InfinityCategories.F2.Ind.LiftedPointQuillenA
public import SerrePositivity.InfinityCategories.F2.Ind.LiftedShapeFilteredCriterion
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FilteredWeakContractibility

/-!
概要：指定始点の下の小さい quasicategory 試験余錐から cofinal 性を得る。
方針：有界な全試験因子化、filtered 弱可縮性、既存の Quillen A を合成する。
規約：元の全射と元の under comma を保持する。
使われ方：一般 accessible 引き戻しの compact 成分射影。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：指定始点の下の各小さい quasicategory 図式が余錐を持てば元の射は right cofinal。
方針：元の under comma の任意の小試験に戻し、filtered 判定と Quillen A を使う。
規約：頂点の被覆だけで cofinal 性を主張しない。
使われ方：全追加入力を保持する交互構成から成分密度を回収する。 -/
lemma isRightCofinal_of_quasicategory_under_tests
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {X Y : SSet.{u + 1}} [Quasicategory X] [Quasicategory Y] (F : X ⟶ Y)
    (hTest : ∀ z : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[0] : SSet.{u}) ⟶ Y,
      ∀ (K : SSet.{u}) (hK : Quasicategory K), letI := hK
        IsKappaSmall μ K → ∀ r : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶
          pullback (sliceUnderProjection z) F, Nonempty (JoinCocone r)) :
    IsRightCofinal F := by
  apply Ind.isRightCofinal_of_weaklyContractible_lifted_point_under
  intro z
  have hfiltered := Ind.isFilteredInfinity_of_liftedShape_cocones (Fact.out : μ.IsRegular)
    (pullback (sliceUnderProjection z) F) (fun hK r ↦
      nonempty_cocone_of_smallQuasicategory_tests hμ
        (fun K hQ hsmall r ↦ hTest z K hQ hsmall r) _ hK r)
  exact isWeaklyContractible_of_isFilteredInfinity _

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
