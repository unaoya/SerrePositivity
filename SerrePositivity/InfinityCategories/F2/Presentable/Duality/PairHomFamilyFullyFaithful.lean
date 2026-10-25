module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.PairEvaluatedTransport
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingPostcompositionLaws
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingPostHomCriterion

/-!
概要：元の全単位関手族そのものの充満忠実性。
方針：同じ単位での評価と元の輸送の比較を、実際の区間 Hom 作用から消去する。
規約：非可逆変換を含む元の全関手圏の作用を証明する。
使われ方：対ごとの反変随伴関手の充満忠実性を共変 Yoneda から回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：元の全単位族の端点を正規化した実 Hom 作用。
方針：元の関手族の区間後合成を使う。
規約：独立な写像空間同値を選ばない。
使われ方：指定単位点での評価による同値性の検出。 -/
def pairUnitHomFamilyIntervalMap {C D : PresentableInfinityObject.{u}}
    (v₀ v₁ : PrLFunctorSpace C D _⦋0⦌) :=
  intervalMappingPostOfEq (pairUnitHomFamily C D) (ULift.up v₀) (ULift.up v₁)
    (pairUnitHomFamily_vertex v₀) (pairUnitHomFamily_vertex v₁)

/-- 概要：同じ全単位族の元の区間 Hom 作用は同値。
方針：元の単位の始対象性による評価と、同じ点での輸送の同値を消去する。
規約：同じ関手の全変換への作用についての結論。
使われ方：元の全単位族の充満忠実性。 -/
lemma pairUnitHomFamilyIntervalMap_isQCatEquivalence
    {C D : PresentableInfinityObject.{u}} (v₀ v₁ : PrLFunctorSpace C D _⦋0⦌) :
    IsQCatEquivalence (pairUnitHomFamilyIntervalMap v₀ v₁) := by
  let w := rightAdjointVertex v₀
  have a : QCatAdjunction (leftVertexFunctor v₀) (rightVertexFunctor w) := by
    simpa only [w, rightAdjointVertex, rightFunctorVertex, rightVertexFunctor,
      Equiv.symm_apply_apply] using chosenRightAdjunction v₀
  let k := pairUnitHomFamilyIntervalMap v₀ v₁
  have hcomp : k ≫
      intervalMappingPostOfEq (evaluateFunctorAt (ULift.up w))
        (functorVertex (pairUnitHomAtLeft v₀)) (functorVertex (pairUnitHomAtLeft v₁))
        (evaluateFunctorAt_functorVertex _ _) (evaluateFunctorAt_functorVertex _ _) =
      intervalMappingPostOfEq (pairUnitHomFamily C D ≫ evaluateFunctorAt (ULift.up w))
        (ULift.up v₀) (ULift.up v₁)
        (pairUnitHomFamily_evaluate_vertex v₀ w) (pairUnitHomFamily_evaluate_vertex v₁ w) := by
    exact intervalMappingPostOfEq_comp _ _ _ _ _ _ _ _
      (pairUnitHomFamily_vertex v₀) (pairUnitHomFamily_vertex v₁)
      (evaluateFunctorAt_functorVertex _ _) (evaluateFunctorAt_functorVertex _ _)
  let z := pairCanonicalUnitFiber v₀ w a
  have e := (pairTransformationEvaluation_parametrizedIso
    (pairUnitHomAtLeft v₀) (pairUnitHomAtLeft v₁) (ULift.up w) z).precomp k
  simp only [← Category.assoc] at e
  rw [hcomp] at e
  have h := pairUnitEvaluatedTransport_isQCatEquivalence v₀ v₁ w a
  have hc : IsQCatEquivalence (k ≫ pairTransformationEvaluation
      (pairUnitHomAtLeft v₀) (pairUnitHomAtLeft v₁) (ULift.up w) z) :=
    h.ofFunctorIso (by simpa only [Category.assoc, z, pairCanonicalUnitPoint] using e.symm)
  exact (pairTransformationEvaluation_isQCatEquivalence
    (pairUnitHomAtLeft v₀) (pairUnitHomAtLeft v₁) (ULift.up w) z
    (pairUnitUnstraighteningVertex_isInitial v₀ w a)).cancel_right hc

/-- 概要：同じ全単位族の元の pinched Hom 作用は同値。
方針：区間 Hom との標準比較を通じて元の作用へ戻す。
規約：元の関手の作用を保持する。
使われ方：充満忠実性の公開。 -/
lemma pairUnitHomFamily_pinchedHomMap_isQCatEquivalence
    {C D : PresentableInfinityObject.{u}} (v₀ v₁ : PrLFunctorSpace C D _⦋0⦌) :
    IsQCatEquivalence (pinchedHomMap (pairUnitHomFamily C D) (ULift.up v₀) (ULift.up v₁)) := by
  apply pinchedHomMap_isQCatEquivalence_of_intervalPost (pairUnitHomFamily C D)
    (ULift.up v₀) (ULift.up v₁) (pairUnitHomFamily_vertex v₀) (pairUnitHomFamily_vertex v₁)
  exact (pinchedHomToIntervalMappingSpace_isQCatEquivalence
    (X := (SSet.uliftFunctor.{u + 2, u + 1}).obj (PrLFunctorSpace C D))
    (ULift.up v₀) (ULift.up v₁)).comp (pairUnitHomFamilyIntervalMap_isQCatEquivalence v₀ v₁)

/-- 概要：構成した元の全単位族は充満忠実。
方針：同じ関手の全ての pinched Hom 作用の同値性を使う。
規約：元の全関手圏の非可逆変換を含む。
使われ方：反変随伴関手の全同値の構成。 -/
lemma pairUnitHomFamily_isFullyFaithful (C D : PresentableInfinityObject.{u}) :
    IsFullyFaithful (pairUnitHomFamily C D) := by
  intro x y
  obtain ⟨x⟩ := x
  obtain ⟨y⟩ := y
  exact (pairUnitHomFamily_pinchedHomMap_isQCatEquivalence x y).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
