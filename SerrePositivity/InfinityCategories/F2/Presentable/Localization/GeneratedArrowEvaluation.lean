module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedArrowColimits
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullSubcomplexEquivalenceLifting
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorEvaluationLifting

/-!
概要：強飽和射圏の包含と端点評価の同値持ち上げ性・小余極限保存性。
方針：射圏内の同型不変性と、公開済みの全部分包含・頂点評価の持ち上げを合成する。
規約：固定始域 fiber の accessibility や presentable 性はまだ主張しない。
使われ方：固定始域 fiber を作る元の射影の fibration 条件。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 射圏の元の全部分包含は同値を持ち上げる。 -/
lemma generatedArrowInclusion_equivalenceLifting (edges : I → C _⦋1⦌) :
    F1B.EquivalenceLifting (generatedArrowInclusion edges) :=
  kanEquivalenceLifting_fullSubcomplexOnVertices_ι _
    (fun e ↦ generatedArrow_mem_iff_vertexIso edges e)

/-- 元の任意の頂点での評価との合成も同値を持ち上げる。 -/
lemma generatedArrowEvaluation_equivalenceLifting (edges : I → C _⦋1⦌)
    (a : (Δ[1] : SSet.{u + 1}) _⦋0⦌) :
    F1B.EquivalenceLifting (generatedArrowInclusion edges ≫ evaluateFunctorAt a) := by
  intro A B i hi he
  have := generatedArrowInclusion_equivalenceLifting edges i hi he
  have := kanEquivalenceLifting_evaluateFunctorAt (X := C) a i hi he
  infer_instance

/-- 強飽和射圏の各端点評価は、元の指定小余錐を保存する。 -/
lemma generatedArrowEvaluation_preservesSmallColimits (hC : HasSmallColimits C)
    (edges : I → C _⦋1⦌) (a : (Δ[1] : SSet.{u + 1}) _⦋0⦌) :
    PreservesSmallColimits (generatedArrowInclusion edges ≫ evaluateFunctorAt a) := by
  intro K D c hc
  have h := evaluateFunctorAt_preservesSmallColimits hC a K
    (D ≫ generatedArrowInclusion edges) (mapJoinCocone (generatedArrowInclusion edges) c)
    (generatedArrowInclusion_preservesSmallColimits hC edges K D c hc)
  exact (isColimitCone_iff_of_cocone_val_eq _ _
    (Category.assoc c.val (generatedArrowInclusion edges) (evaluateFunctorAt a))).mpr h

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
