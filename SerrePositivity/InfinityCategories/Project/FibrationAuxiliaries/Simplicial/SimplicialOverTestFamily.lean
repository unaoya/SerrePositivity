module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplicialEnrichedOpposite
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplicialPairNerve
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplicialOverTestComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorSpaceCurrying
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.UniversalCoherentReconstructionComponents

/-!
概要：二変数の相対 Hom の共同評価を、関手圏に値を取る反変な族へ移す。
方針：豊穣圏の積の coherent nerve の同型で引き戻し、変数を交換して curry する。
規約：各頂点では相対 Hom の coherent 評価全体を厳密に回収する。
使われ方：自然な復元 span のテスト同型から全空間側の比較を回収する際の表現可能な族。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial

/-- 全標的への相対 Hom の coherent 評価を始域に反変な関手圏値の族にする。 -/
def simplicialOverTestFamily {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C] {B : SSet.{u}}
    (F : EnrichedFunctor SSet.{u} C (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplicialOverObject B)) :
    SimplicialNerve Cᵒᵖ ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity B)).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  curry ((β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity B) (SimplicialNerve Cᵒᵖ)).hom ≫
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialPairNerveFrom Cᵒᵖ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialOverJointTest F)

/-- 反変な族の頂点での制限は、同じ始域から全標的への既存の評価。 -/
lemma simplicialOverTestFamily_restrict {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C] {B : SSet.{u}}
    (F : EnrichedFunctor SSet.{u} C (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplicialOverObject B)) (X : C) :
    lift (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity B)) (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op X))) ≫
      uncurry (simplicialOverTestFamily F) = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationCoherentEvaluation (F.obj X).val := by
  rw [simplicialOverTestFamily, uncurry_curry]
  change (lift (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity B))
    (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op X))) ≫
    (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity B) (SimplicialNerve Cᵒᵖ)).hom) ≫
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialPairNerveFrom Cᵒᵖ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialOverJointTest F = _
  rw [lift_braiding_hom, ← Category.assoc]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity]
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialPairNerveFrom_right, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialOverJointTest_right]

/-- 反変な族の実際の頂点は、既存の coherent 評価の関手頂点そのもの。 -/
lemma simplicialOverTestFamily_vertex {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C] {B : SSet.{u}}
    (F : EnrichedFunctor SSet.{u} C (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplicialOverObject B)) (X : C) :
    (simplicialOverTestFamily F).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op X)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationCoherentEvaluation (F.obj X).val) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.functorVertex_uncurry_at_vertex (simplicialOverTestFamily F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op X))).symm.trans
      (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (simplicialOverTestFamily_restrict F X))

/-- 前合成同値な自然な比較は、関手圏に値を取る全始域の族の同型になる。 -/
def SimplicialOverComparison.testFamilyIso {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C] {B : SSet.{u}} [Quasicategory B]
    {F G : EnrichedFunctor SSet.{u} C (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplicialOverObject B)}
    (η : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplicialOverComparison F G)
    (h : ∀ X, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (η.val X).left) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (simplicialOverTestFamily G) (simplicialOverTestFamily F) :=
  ((η.jointTestIso h).precomp
    ((β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity B) (SimplicialNerve Cᵒᵖ)).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialPairNerveFrom Cᵒᵖ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B))).curry

/-- left fibrations の各対象を、その対象から全標的への Hom 関手へ送る反変な族。 -/
def leftFibrationHomTestFamily (B : SSet.{u}) :
    SimplicialNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B)ᵒᵖ ⟶
      (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity B)).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  simplicialOverTestFamily (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.leftFibrationOverEnriched B)

/-- left fibration 値の豊穣関手のテスト族は、標準 Hom の族の前合成そのもの。 -/
lemma simplicialOverTestFamily_leftFibration {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C] {B : SSet.{u}}
    (F : EnrichedFunctor SSet.{u} C (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B)) :
    simplicialOverTestFamily (F.comp SSet (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.leftFibrationOverEnriched B)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialEnrichedOpposite F) ≫ leftFibrationHomTestFamily B := by
  apply uncurry_injective
  rw [uncurry_natural_left]
  simp only [leftFibrationHomTestFamily, simplicialOverTestFamily, uncurry_curry]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨q, p⟩
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro i j
  simp only [eqToHom_refl, Category.comp_id]

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial
