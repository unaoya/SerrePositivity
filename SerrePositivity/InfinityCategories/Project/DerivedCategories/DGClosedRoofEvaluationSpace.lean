module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeRoofEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofEvaluationUniversalFiber
/-!
概要：指定実閉分母と係数族の任意標的への実評価を、全境界充填する一つの空間に束ねる。
方針：実分母から恒等分母への同じ底 prism と、元の実屋根族を評価 lift 空間に代入する。
規約：全空間上の普遍実評価は選択点ごとに取り直さない。使われ方：相対高次整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
variable (P : Set D) (x y : D) {K Y : SSet.{max u v}} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y)
variable (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x)
variable (n : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D (ForgetEnrichment.to (Complex A) r.obj.left) y)
/-- 元の閉分母表示の、指定標的における同じ実屋根族。 -/
def dgClosedRoofEvaluationStart :=
  (n ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y r) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap A D P x y F
/-- 指定実閉分母から恒等分母への同じ全時刻の底 prism。 -/
def dgClosedRoofEvaluationPrism :=
  (β_ (Δ[1] : SSet.{max u v}) K).hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedDenominatorHomotopy A D P x r K).h
/-- 元の実屋根族は、同じ指定底 prism の始端上に厳密に重なる。 -/
lemma dgClosedRoofEvaluation_square :
    dgClosedRoofEvaluationStart A D P x y F r n ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofProjection A D P x F
      (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ dgClosedRoofEvaluationPrism A D P x r := by
  have ha : dgClosedRoofEvaluationStart A D P x y F r n ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofProjection A D P x F
        (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex A D P x r) := by
    dsimp only [dgClosedRoofEvaluationStart]
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap_projection, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion_projection, SSet.comp_const]
  exact ha.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedDenominatorHomotopy A D P x r K).h₀.symm
/-- 指定実閉分母・係数族の、全実評価と全比較をパラメータ化する空間。 -/
def dgClosedRoofEvaluationSpace : SSet.{max u v} :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEvaluationLiftSpace (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofProjection A D P x F
    (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)))
    (dgClosedRoofEvaluationStart A D P x y F r n) (dgClosedRoofEvaluationPrism A D P x r)
    (dgClosedRoofEvaluation_square A D P x y F r n)
/-- 任意反転標的の全実評価空間は、任意次元の境界を充填する可縮 Kan 複体。 -/
lemma dgClosedRoofEvaluationSpace_isContractibleKan [Quasicategory Y]
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (dgClosedRoofEvaluationSpace A D P x y F r n) := by
  have := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofProjection_leftFibration A D P x F hF
    (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEvaluationLiftSpace_isContractibleKan _ _ _ _
/-- 全評価選択空間上で、同じ全円柱を保つ恒等分母 fiber への普遍実評価。 -/
def dgClosedRoofUniversalFiberEvaluation :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofUniversalFiberEvaluation (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofProjection A D P x F
      (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverIdentityVertex A D P x)
      (dgClosedRoofEvaluationStart A D P x y F r n) (dgClosedRoofEvaluationPrism A D P x r)
      (dgClosedRoofEvaluation_square A D P x y F r n) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEvaluationUniversalFiber _ _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedDenominatorHomotopy A D P x r K).h₁
end SerrePositivity.InfinityCategories.Project.DerivedCategories
