module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowEvaluationCofinality
public import SerrePositivity.InfinityCategories.F2.Ind.IndContinuousLeftKan
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorCoconePointwiseCriterion
/-!
概要：元の射図式を頂点とする小さい表示添字の標準全余錐は、関手圏内の余極限。
方針：両端評価の cofinal 性で元の scalar 密度余錐へ戻し、点ごとの余極限判定を使う。
規約：元の全余錐と頂点 D を選び直さず、モデル圏の仮定を要求しない。
使われ方：射形状の単一 κ-filtered 表示と有限半順序形状への帰納。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
/-- 概要：元の scalar Ind comma の同じ標準密度余錐は余極限。
方針：元の小さい元の圏への比較同値で制限する。
規約：元の全余錐を保持。使われ方：各点の標準余錐の普遍性。 -/
lemma indYonedaCanonicalCocone_isColimit (v : (IndInfinity κ C) _⦋0⦌) :
    IsColimitCone (leftKanCanonicalCocone (indYoneda κ C) (𝟙 (IndInfinity κ C)) v) := by
  apply (isColimitCone_iff_restrict_equivalentShape (indElementsLeftKanComparison κ v)
    (indElementsLeftKanComparison_isQCatEquivalence κ v) _).mpr
  have h : ((leftKanCanonicalCocone (indYoneda κ C) (𝟙 (IndInfinity κ C)) v).restrict
      (indElementsLeftKanComparison κ v)).val = (indVertexDensityCocone κ v).val := by
    rw [indLeftKanCanonicalCocone_restrict_val]
    simp only [mapJoinCocone, Category.comp_id]
  exact (F2.isColimitCone_iff_of_cocone_val_eq _ _ h).mpr
    (indVertexDensityCocone_isColimit κ v)
variable [Fact κ.IsRegular]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C)
/-- 概要：同じ小さい表示添字の全余錐の任意の頂点評価は余極限。
方針：元の cofinal な評価で scalar 密度余錐を制限する。
規約：評価した元の全射を保持。使われ方：関手圏の点ごとの判定。 -/
lemma smallDiagramCommaCocone_evaluate_isColimit (k : (Δ[1] : SSet.{u}) _⦋0⦌) :
    IsColimitCone (F1B.kanPostcomposeCocone
      (evaluateFunctorAt (ULift.up k)) (smallDiagramCommaCocone κ D)) := by
  let c := leftKanCanonicalCocone (indYoneda κ C) (𝟙 (IndInfinity κ C))
    (D.app (Opposite.op ⦋0⦌) (ULift.up k))
  have hc : IsColimitCone (c.restrict (smallDiagramCommaEvaluation κ D k)) :=
    (isColimitCone_iff_restrict_rightCofinal (smallDiagramCommaEvaluation κ D k)
      (smallDiagramCommaEvaluation_interval_isRightCofinal κ D k) c).mp
      (indYonedaCanonicalCocone_isColimit κ _)
  have hval : (c.restrict (smallDiagramCommaEvaluation κ D k)).val =
      (F1B.kanPostcomposeCocone (evaluateFunctorAt (ULift.up k))
        (smallDiagramCommaCocone κ D)).val := smallDiagramCommaEvaluation_coconeMap κ D k
  exact (F2.isColimitCone_iff_of_cocone_val_eq _ _ hval).mp hc
/-- 概要：元の射図式 D を頂点とする、同じ小さい添字の標準全余錐は余極限。
方針：全頂点評価の余極限性を使う。
規約：元の余錐と頂点を保持。使われ方：単一 filtered 射図式表示。 -/
lemma smallArrowDiagramCommaCocone_isColimit : IsColimitCone (smallDiagramCommaCocone κ D) := by
  apply F2.isColimitCone_functor_of_pointwise
  intro k
  rcases k with ⟨k⟩
  exact smallDiagramCommaCocone_evaluate_isColimit κ D k
end SerrePositivity.InfinityCategories.F2.Ind
