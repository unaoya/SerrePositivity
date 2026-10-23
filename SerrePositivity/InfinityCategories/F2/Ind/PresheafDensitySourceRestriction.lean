module

public import SerrePositivity.InfinityCategories.F2.Ind.PresheafDensityEvaluation
public import SerrePositivity.InfinityCategories.F1.Transport.PointFunctorEvaluation

/-!
概要：元の共同 Hom の二変数の底を始点固定に制限し、同じ密度評価図式を厳密に回収する。
方針：元の curry の評価公式と、宇宙持ち上げと積の交換の座標を使う。
規約：元の全図式を使い、値ごとの同型で代用しない。
使われ方：大域密度変換の unstraightening の底変換自然性への入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)
local notation "E" => smallRightUnstraightening F
local notation "p" => smallRightUnstraighteningProjection F

/-- 始点を元の対象に固定し、元の小さい元の圏を第二変数として保つ底の包含。 -/
def presheafDensitySourceInclusion : E ⟶ C.op ⊗ E :=
  lift (SSet.const (SSet.opObjEquiv.symm x)) (𝟙 E)

/-- 同じ共同 Hom の始点固定は、元の Yoneda 図式の同じ評価そのもの。 -/
lemma presheafDensitySourceInclusion_source :
    (SSet.uliftFunctor.{u + 1, u}).map (presheafDensitySourceInclusion F x) ≫
      twistedElementsHomDiagram p = presheafDensityEvaluationDiagram F x := by
  rw [presheafDensityEvaluationDiagram, ← presheafDensity_source_curry F]
  change _ = curry
    ((HomotopyLimits.uliftTensorIso.{u, u + 1} C.op E).inv ≫
      twistedElementsHomDiagram p) ≫
    evaluateFunctorAt (ULift.up (SSet.opObjEquiv.symm x))
  rw [curry_evaluateFunctorAt_vertex]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro z
  rfl

omit [Quasicategory C] in
/-- 同じ標的図式の始点固定は、元の F の指定値に定値な図式そのもの。 -/
lemma presheafDensitySourceInclusion_target :
    (SSet.uliftFunctor.{u + 1, u}).map (presheafDensitySourceInclusion F x) ≫
      presheafTwistedElementsTargetDiagram F =
        SSet.const (presheafDensityEvaluationVertex F x) := by
  have hk : (SSet.uliftFunctor.{u + 1, u}).map (presheafDensitySourceInclusion F x) ≫
      (SSet.uliftFunctor.{u + 1, u}).map (fst C.op E) =
      SSet.const (ULift.up (SSet.opObjEquiv.symm x)) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    rfl
  rw [presheafTwistedElementsTargetDiagram, ← Category.assoc, hk, SSet.const_comp,
    presheafDensityEvaluationVertex_value]

end SerrePositivity.InfinityCategories.F2.Ind
