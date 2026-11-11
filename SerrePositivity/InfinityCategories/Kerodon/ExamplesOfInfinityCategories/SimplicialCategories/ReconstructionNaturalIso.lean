module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.ReconstructionHomRecovery
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.OppositeFunctorIso

/-!
概要：元の left fibrations の全空間で、weighted nerve による復元自己関手と恒等を比較する。
方針：全 Hom の族から回収した同型を、coherent nerve と単体集合の二つの反転で戻す。
規約：指定された元の復元自己関手を保持し、対象ごとの厳密化の自然性は仮定しない。
使われ方：strict transport と分類図式の自然な単位の主経路。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

local instance {B : SSet.{u}} :
    ∀ X Y : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B)ᵒᵖ, KanComplex (SimplicialCategory.sHom X Y) :=
  fun X Y ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom Y.unop X.unop))

/-- 元の全 left fibrations の恒等関手と weighted nerve の復元自己関手の自然な同型。 -/
def leftStrictTransportReconstructionNaturalIso (C : Type u) [Category.{u} C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity (nerve C)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.strictTransportWeightedEnriched C)) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject (nerve C))
  let F := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.strictTransportWeightedEnriched C
  have hn : SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap F) ≫ e.hom =
      e.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialEnrichedOpposite F) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeMap_post F
  have hr : e.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialEnrichedOpposite F) ≫ e.inv =
      SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap F) := by
    rw [← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h := ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.leftStrictTransportReconstructionOppositeIso C).precomp e.hom).postcomp e.inv
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((e.hom ≫ 𝟙 _) ≫ e.inv)
    ((e.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialEnrichedOpposite F)) ≫ e.inv) at h
  simp only [Category.assoc, Category.id_comp, Iso.hom_inv_id, hr] at h
  have n : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (SSet.opFunctor.map (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity (nerve C))))
      (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap F)) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (SSet.opFunctor.map (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity (nerve C))))
      (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap F)) at h
    exact h
  exact n.unop

/-- 同じ全空間の復元同型の、実際の単体的ホモトピー。 -/
def leftStrictTransportReconstructionNaturalHomotopy (C : Type u) [Category.{u} C] :
    SSet.Homotopy (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity (nerve C)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.strictTransportWeightedEnriched C)) :=
  (leftStrictTransportReconstructionNaturalIso C).simplicialHomotopy

/-- 復元同型の終域は、元の strict transport、図式の包含、weighted nerve の合成そのもの。 -/
lemma strictTransportWeightedEnriched_coherentMap (C : Type u) [Category.{u} C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.strictTransportWeightedEnriched C) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStrictTransportInfinityMap C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictTransportKanDiagramEnriched ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveInfinityMap C := rfl

/-- 実際の三つの比較射による全空間の復元は、恒等関手と自然に同型。 -/
def leftStrictTransportWeightedNerveNaturalIso (C : Type u) [Category.{u} C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity (nerve C)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStrictTransportInfinityMap C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictTransportKanDiagramEnriched ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveInfinityMap C) := by
  rw [← strictTransportWeightedEnriched_coherentMap]
  exact leftStrictTransportReconstructionNaturalIso C

/-- 全空間の同じ復元自己関手そのものは同値であり、対象ごとの逆を必要としない。 -/
lemma strictTransportWeightedEnriched_coherentMap_isQCatEquivalence
    (C : Type u) [Category.{u} C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.strictTransportWeightedEnriched C)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsQCatEquivalence.ofFunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (Iso.refl (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity (nerve C)))).isQCatEquivalence
    (leftStrictTransportReconstructionNaturalIso C)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
