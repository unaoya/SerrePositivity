module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeHomCoherentEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence

/-!
概要：実際の標準 Hom の族は、全写像空間の意味で充満忠実。
方針：元の主比較から標準 Hom 比較と端点の同型を消去する。
規約：独立な写像空間同値で作用を置き換えず、実際の pinchedHomMap を使う。
使われ方：復元自己関手の Hom の族の同型を全空間側へ戻す。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

local instance {B : SSet.{u}} :
    ∀ X Y : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B)ᵒᵖ, KanComplex (SimplicialCategory.sHom X Y) :=
  fun X Y ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom Y.unop X.unop))

/-- 標準 Hom の族の実際の写像空間作用は、元の主比較の同値性により同値。 -/
lemma leftFibrationHomTestFamily_pinchedHomMap_isQCatEquivalence {B : SSet.{u}}
    (a q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.leftFibrationHomTestFamily B)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op q)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op a))) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomCoherentComparison_isQCatEquivalence a q
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison (Opposite.op q) (Opposite.op a) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.leftFibrationHomTestFamily B)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op q)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op a)) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomCoherentEndpointIso a q).hom) at h
  have n := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison_isQCatEquivalence (Opposite.op q) (Opposite.op a)).cancel_left h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomCoherentEndpointIso a q)).isQCatEquivalence.cancel_right n

/-- 元の全 left fibrations の標準 Hom の族は、実際の全写像空間上で充満忠実。 -/
lemma leftFibrationHomTestFamily_isFullyFaithful (B : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.leftFibrationHomTestFamily B) := by
  intro x y
  obtain ⟨q, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertexEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B)ᵒᵖ).surjective x
  obtain ⟨a, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertexEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B)ᵒᵖ).surjective y
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence.isSimplicialHomotopyEquivalence
    (leftFibrationHomTestFamily_pinchedHomMap_isQCatEquivalence a.unop q.unop)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
