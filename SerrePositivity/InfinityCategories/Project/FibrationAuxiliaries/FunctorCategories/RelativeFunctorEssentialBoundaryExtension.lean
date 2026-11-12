module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorBoundaryCorrection

/-!
概要：前合成同値に沿う相対延長で指定した単射境界を厳密に保持する。
方針：同型まで延長してから単射境界の制限の left fibration で修正する。
規約：比較射自体の単射性は不要。
使われ方：coherent な prism の collage への延長の両端を固定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 概要：前合成同値に沿う相対延長は単射の共通境界上で厳密に固定できる。
方針：境界に制限した同型を持ち上げ全体の相対射を修正する。
規約：i は単射でなくてもよく、境界の A への合成 j≫i に単射性を要求する。
使われ方：元の coherent な変換と指定両端を保持した collage の pointed な図式。 -/
lemma exists_relativeFunctorEssential_boundary_extension
    {A D C E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (b : A ⟶ B) (i : D ⟶ A) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence i)
    (j : C ⟶ D) [Mono (j ≫ i)] (W : D ⟶ E) (hW : W ≫ p = i ≫ b) :
    ∃ (L : A ⟶ E) (hL : L ≫ p = b), (j ≫ i) ≫ L = j ≫ W ∧
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (i ≫ b) (i ≫ L) (by rw [Category.assoc, hL]))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (i ≫ b) W hW)) := by
  obtain ⟨L, hL, ⟨e⟩⟩ :=
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.exists_relativeFunctorExtension_of_precompositionEquivalence p b i hi W hW
  have hWj : (j ≫ W) ≫ p = (j ≫ i) ≫ b := by
    rw [Category.assoc, hW, Category.assoc]
  have eb : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p ((j ≫ i) ≫ b) ((j ≫ i) ≫ L)
        (by rw [Category.assoc, hL]))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p ((j ≫ i) ≫ b) (j ≫ W) hWj) := by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p (i ≫ b) j)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorPre_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorPre_vertex] at h
    have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map h
      (eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p) (Category.assoc j i b).symm))
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex_transport p (Category.assoc j i b).symm,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex_transport p (Category.assoc j i b).symm] at ht
    simpa only [Category.assoc] using ht
  obtain ⟨L', hL', heq, ⟨η⟩⟩ :=
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.exists_relativeFunctor_boundary_correction p b (j ≫ i) L hL (j ≫ W) hWj eb
  have ηi := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map η (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p b i)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorPre_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorPre_vertex] at ηi
  exact ⟨L', hL', heq, ⟨ηi.symm ≪≫ e⟩⟩

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
