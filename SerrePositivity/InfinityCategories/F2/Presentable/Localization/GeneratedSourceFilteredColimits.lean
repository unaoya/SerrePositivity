module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceFiberEquivalence
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedArrowEvaluation
public import SerrePositivity.InfinityCategories.F2.Presentable.PointFiberFilteredColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.EquivalenceColimits
public import SerrePositivity.InfinityCategories.F1B.Cofinality.CofinalVertexFiberPullback

/-!
概要：固定始域の閉包内射圏は、全ての正則濃度で小 filtered 余極限を持つ。
方針：P の公開 point-fiber 版を元の始点評価へ適用し、既存の厳密 fiber 比較で輸送する。
規約：射圏全体の accessibility・filtered 生成表示は仮定も結論もしない。
使われ方：固定始域圏の小余完備性と accessibility の生成部分を分ける。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 同じ元の始点評価の、指定点包含への通常の pullback。 -/
def generatedSourcePointPullback (edges : I → C _⦋1⦌) (x : C _⦋0⦌) : SSet.{u + 1} :=
  pullback (generatedArrowInclusion edges ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0))
    (SSet.yonedaEquiv.symm x)

instance generatedSourcePointPullback_quasicategory (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    Quasicategory (generatedSourcePointPullback edges x) := by
  have hp : F1B.EquivalenceLifting
      (generatedArrowInclusion edges ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)) :=
    generatedArrowEvaluation_equivalenceLifting edges (stdSimplex.obj₀Equiv.symm 0)
  have := hp.innerFibration
  exact quasicategory_pullback_of_innerFibration_left _ _

/-- 全 coslice の同じ比較から、点包含への通常の pullback への同値を得る。 -/
def generatedSourcePointPullbackEquivalence (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    QCatEquivalence (generatedSourceCategory edges x) (generatedSourcePointPullback edges x) :=
  (generatedSourceToArrowFiber_isQCatEquivalence edges x).choose.trans
    (qCatEquivalenceOfIso (cofinalVertexFiberPullbackIso _ x))

/-- 同じ通常の pullback への同値は、元の全脚族を第一射影で回収する。 -/
lemma generatedSourcePointPullbackEquivalence_fst (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    (generatedSourcePointPullbackEquivalence edges x).hom ≫
      pullback.fst (generatedArrowInclusion edges ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0))
        (SSet.yonedaEquiv.symm x) = generatedSourceArrows edges x := by
  change (generatedSourceToArrowFiber edges x ≫ (cofinalVertexFiberPullbackIso _ x).hom) ≫ _ = _
  rw [Category.assoc, cofinalVertexFiberPullbackIso_hom_fst, generatedSourceToArrowFiber_inclusion]

/-- 固定始域圏には、任意の正則濃度の元の小 filtered 余極限が存在する。 -/
lemma generatedSource_hasSmallKappaFilteredColimits {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    (hC : HasSmallColimits C) (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    Ind.HasSmallKappaFilteredColimits κ (generatedSourceCategory edges x) := by
  have h := fiber_hasSmallKappaFilteredColimits hκ
    (generatedArrowInclusion edges ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0))
    (SSet.yonedaEquiv.symm x) (generatedArrowEvaluation_equivalenceLifting edges _)
    ((generatedArrow_hasSmallColimits hC edges).hasSmallKappaFilteredColimits κ)
    ((generatedArrowEvaluation_preservesSmallColimits hC edges _).isKappaAccessibleFunctor κ)
  exact hasSmallKappaFilteredColimits_of_equivalence
    (generatedSourcePointPullbackEquivalence edges x).symm h

/-- 固定始域の元の全脚族は、同じ濃度の小 filtered 余極限を保存する。 -/
lemma generatedSourceArrows_isKappaAccessibleFunctor {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    (hC : HasSmallColimits C) (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    IsKappaAccessibleFunctor κ (generatedSourceArrows edges x) := by
  have hf := fiber_fst_isKappaAccessibleFunctor hκ
    (generatedArrowInclusion edges ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0))
    (SSet.yonedaEquiv.symm x) (generatedArrowEvaluation_equivalenceLifting edges _)
    ((generatedArrow_hasSmallColimits hC edges).hasSmallKappaFilteredColimits κ)
    ((generatedArrowEvaluation_preservesSmallColimits hC edges _).isKappaAccessibleFunctor κ)
  have he := equivalence_preservesSmallKappaFilteredColimits κ
    (generatedSourcePointPullbackEquivalence edges x).isQCatEquivalence
  have h := he.comp hf
  rwa [generatedSourcePointPullbackEquivalence_fst] at h

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
