module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.FunctorColimitConeExistence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.CoherentTotalColimit

/-!
概要：小さい底上の元の前層値 coherent 図式に、全評価が余極限となる実際の全余錐を供給。
方針：各空間値評価図式の元の全空間余極限を、関手圏の点ごとの存在定理へ入力する。
規約：元の図式と全評価点を保持。sifted 性や底の quasicategory 性は不要。
使われ方：P_Σ の sifted 閉性で、前層圏内の指定余極限錐を供給する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable {B C : SSet.{u}}
  (r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C)

/-- 元の小さい前層値 coherent 図式には、全ての評価が余極限となる全余錐が存在する。 -/
lemma presheafCoherentColimitCone_exists :
    ∃ q : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone q ∧
      ∀ x : ((SSet.uliftFunctor.{u + 1, u}).obj C.op) _⦋0⦌,
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x) q) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.exists_colimitCone_functor_of_pointwise r
    (fun x ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.hasColimit_coherentSpaceDiagram (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x))

/-- 元の全図式上に、全ての評価が余極限となる前層圏の実際の余極限全余錐を選ぶ。 -/
def presheafCoherentColimitCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r :=
  Classical.choose (presheafCoherentColimitCone_exists r)

/-- 選んだ同じ元の全余錐は、前層圏内の余極限全余錐。 -/
lemma presheafCoherentColimitCone_isColimit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (presheafCoherentColimitCone r) :=
  (Classical.choose_spec (presheafCoherentColimitCone_exists r)).1

/-- 選んだ同じ元の全余錐を各点で評価した全余錐は、同じ評価図式の余極限。 -/
lemma presheafCoherentColimitCone_evaluation_isColimit
    (x : ((SSet.uliftFunctor.{u + 1, u}).obj C.op) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x)
      (presheafCoherentColimitCone r)) :=
  (Classical.choose_spec (presheafCoherentColimitCone_exists r)).2 x

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
