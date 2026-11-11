module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorEssentialExtension

/-!
概要：指定した元の底図式を固定して、前合成同値に沿う相対射を降下する。
方針：Over 圏の元の射を使い、相対制限の本質的全射性を実射へ戻す。
規約：底上の等号を厳密に保ち、制限の比較も同じ相対関手空間内で返す。
使われ方：cocartesian scaffold 上の指定全族単位を元の全空間へ降ろす。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 元の底を固定した相対降下は、同じ元の相対制限の同型も保持する。 -/
lemma exists_relativeFunctorExtension_over_of_precompositionEquivalence
    {A D E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (b : A ⟶ B) (r : D ⟶ B) (i : D ⟶ A) (hi : i ≫ b = r)
    (ei : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence i) (W : D ⟶ E) (hW : W ≫ p = r) :
    ∃ (L : A ⟶ E) (hL : L ≫ p = b),
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p r (i ≫ L) (by rw [Category.assoc, hL, hi]))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p r W hW)) := by
  let j : Over.mk r ⟶ Over.mk b := Over.homMk i hi
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeFunctorOverPre_isQCatEquivalence p j ei
  obtain ⟨v, ⟨e⟩⟩ := he.choose.isEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p r W hW)
  obtain ⟨L, hL, hv⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_relativeFunctorVertex p b v
  rw [← hv] at e
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p j).app _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (Over.mk b).hom L hL))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p r W hW) at e
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre_vertex p j L hL] at e
  exact ⟨L, hL, ⟨e⟩⟩

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
