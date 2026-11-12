module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.HomInfinityBifunctor
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HomCovariantComparison

/-!
概要：元の関手 F の Hom(F(−), d) を、一つの全前層値関手として構成する。
方針：元の Yoneda 関手を、元の F に沿う前層制限で後合成する。
規約：標的 d に関する全自然性を保持し、対象ごとの Hom 同値で代用しない。
使われ方：P_Σ 左 Kan 延長の全自然 Hom 表示の係数前層。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable {C D : SSet.{u}} [Quasicategory D]

/-- 元の Hom(F(−), d) を、d の全前層値図式として束ねた係数関手。 -/
def presheafHomWeightDiagram (F : C ⟶ D) :
    (SSet.uliftFunctor.{u + 1, u}).obj D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityRestriction F

/-- 同じ係数前層族の全二変数評価は、元の F を前合成した元の共同 Hom 評価。 -/
lemma presheafHomWeightDiagram_uncurry (F : C ⟶ D) :
    uncurry (presheafHomWeightDiagram F) =
      ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map F) ▷
        (SSet.uliftFunctor.{u + 1, u}).obj D) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homInfinityJointEvaluation D := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_uncurry]
  apply SSet.hom_ext
  intro n
  rfl

/-- 同じ全係数族の二変数を交換すると、元の F の反転に沿う全 co-Yoneda 族となる。 -/
lemma presheafHomWeightDiagram_transpose (F : C ⟶ D) :
    curry ((β_ ((SSet.uliftFunctor.{u + 1, u}).obj D)
      ((SSet.uliftFunctor.{u + 1, u}).obj C.op)).hom ≫
        uncurry (presheafHomWeightDiagram F)) =
      (SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap D := by
  apply uncurry_injective
  rw [uncurry_curry, uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap_uncurry,
    presheafHomWeightDiagram_uncurry]
  apply SSet.hom_ext
  intro n
  rfl

/-- 同じ全係数関手の点評価は、元の F の像を始点とする同じ全 Hom 関手。 -/
lemma presheafHomWeightDiagram_evaluation (F : C ⟶ D) (c : C _⦋0⦌) :
    presheafHomWeightDiagram F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityEvaluation c =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (F.app (Opposite.op ⦋0⦌) c) := by
  rw [presheafHomWeightDiagram, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityRestriction_evaluation,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant_eq_yonedaEvaluation]

/-- 元の同じ係数前層の評価と、元の全共変表現可能関手との全自然比較。 -/
def presheafHomWeightDiagram_evaluationIso (F : C ⟶ D) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (presheafHomWeightDiagram F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityEvaluation c)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity (F.app (Opposite.op ⦋0⦌) c)) := by
  rw [presheafHomWeightDiagram_evaluation]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.homInfinityCovariant_covariantIso _

/-- 元の係数前層の指定頂点は、元の表現可能前層に元の F を前合成した全関手。 -/
lemma presheafHomWeightDiagram_vertex (F : C ⟶ D) (d : D _⦋0⦌) :
    (presheafHomWeightDiagram F).app (Opposite.op ⦋0⦌) (ULift.up d) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map F) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity d) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityRestriction F).app _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap D).app _ (ULift.up d)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_vertex]
  rfl

/-- 元の係数関手は、元の関手への前合成を同じ前層制限へ厳密に写す。 -/
lemma presheafHomWeightDiagram_precomp {B : SSet.{u}} (f : B ⟶ C) (F : C ⟶ D) :
    presheafHomWeightDiagram (f ≫ F) =
      presheafHomWeightDiagram F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityRestriction f := by
  rw [presheafHomWeightDiagram, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityRestriction_comp]
  exact (Category.assoc _ _ _).symm

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
