module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexTwoEvaluationFactor
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedHomTriangleCompositeMorphism

/-!
概要：元の Ncomp の値照合を、同じ二固定射の指定評価比較の合成則へ正確に帰着する。
方針：凍結点の無条件な二評価因子式を両方向に使う。
規約：帰着先の等式は未証明であり、交換入力の代用とはしない。
使われ方：指定値の合成則を証明した後、元の raw 三角形へ戻す接続点。
-/

@[expose] public section
noncomputable section
universe u
open SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "s" => coherentColimitApexTriangle B T
local notation "f" => coherentEdgeHom (SpaceInfinity.δ 2 s)
local notation "g" => coherentEdgeHom (SpaceInfinity.δ 0 s)

/-- 元の零面値と raw 二辺値の Ncomp は、同じ二射の指定評価の合成則と同値。 -/
lemma coherentColimitApexZeroCompositeValue_heq_composite_iff :
    HEq (coherentColimitApexZeroCompositeValue B T)
      (pointedHomCompositeMorphismEvaluationComparison f g) ↔
    HEq (pointedHomTwoMorphismEvaluationComparison f g)
      (pointedHomCompositeMorphismEvaluationComparison f g) := by
  have h := coherentColimitApexZeroCompositeValue_heq_two_evaluation B T
  exact ⟨fun e => h.symm.trans e, fun e => h.trans e⟩

/-- 同じ帰着は、元の全三角形の二辺評価比較も値を変えずに保持する。 -/
lemma coherentColimitApexZeroCompositeValue_heq_triangle_iff :
    HEq (coherentColimitApexZeroCompositeValue B T)
      (pointedHomTriangleCompositeEvaluationComparison s) ↔
    HEq (pointedHomTwoMorphismEvaluationComparison f g)
      (pointedHomCompositeMorphismEvaluationComparison f g) := by
  rw [pointedHomTriangleCompositeEvaluationComparison_eq_morphism]
  exact coherentColimitApexZeroCompositeValue_heq_composite_iff B T

end SerrePositivity.InfinityCategories.F2
