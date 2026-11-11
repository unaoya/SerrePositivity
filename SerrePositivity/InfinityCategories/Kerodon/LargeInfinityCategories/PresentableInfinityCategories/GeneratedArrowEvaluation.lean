module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.GeneratedArrowColimits
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullSubcomplexEquivalenceLifting
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorEvaluationLifting

/-!
概要：強飽和射圏の包含と端点評価の同値持ち上げ性・小余極限保存性。
方針：射圏内の同型不変性と、公開済みの全部分包含・頂点評価の持ち上げを合成する。
規約：固定始域 fiber の accessibility や presentable 性はまだ主張しない。
使われ方：固定始域 fiber を作る元の射影の fibration 条件。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 射圏の元の全部分包含は同値を持ち上げる。 -/
lemma generatedArrowInclusion_equivalenceLifting (edges : I → C _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowInclusion edges) :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.kanEquivalenceLifting_fullSubcomplexOnVertices_ι _
    (fun e ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrow_mem_iff_vertexIso edges e)

/-- 元の任意の頂点での評価との合成も同値を持ち上げる。 -/
lemma generatedArrowEvaluation_equivalenceLifting (edges : I → C _⦋1⦌)
    (a : (Δ[1] : SSet.{u + 1}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowInclusion edges ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a) := by
  intro A B i hi he
  have := generatedArrowInclusion_equivalenceLifting edges i hi he
  have := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.kanEquivalenceLifting_evaluateFunctorAt (X := C) a i hi he
  infer_instance

/-- 強飽和射圏の各端点評価は、元の指定小余錐を保存する。 -/
lemma generatedArrowEvaluation_preservesSmallColimits (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (edges : I → C _⦋1⦌) (a : (Δ[1] : SSet.{u + 1}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowInclusion edges ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a) := by
  intro K D c hc
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorSmallColimits.evaluateFunctorAt_preservesSmallColimits hC a K
    (D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowInclusion edges) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowInclusion edges) c)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowInclusion_preservesSmallColimits hC edges K D c hc)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _
    (Category.assoc c.val (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowInclusion edges) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a))).mpr h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
