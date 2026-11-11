module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionDiagonal
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.MixedHomVertices

/-!
概要：QCat の同じ豊穣合成を、元の内部 Hom の後合成作用と同定する。
方針：各単体の core の元の値を比較する。
規約：同じ元の後合成と宇宙持ち上げを使う。
使われ方：合成三角形全体への比較を、元の後合成と対角評価の四角形へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 元の QCat の固定第二射による豊穣合成は、内部 Hom の後合成の core そのもの。 -/
lemma qCatCoherentCompositionFixedParameter_comp (A B Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}) (f : B ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionFixedParameter A B Z f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComposition A B Z =
      (SSet.uliftFunctor.{u + 1, u}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((ihom A.obj).map (show B.obj ⟶ Z.obj from f))) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨s⟩
  apply ULift.ext
  apply Subtype.ext
  have h : (ρ_ ((ihom A.obj).obj B.obj)).inv ≫
      ((ihom A.obj).obj B.obj) ◁ curry' (C := SSet.{u}) f ≫
        MonoidalClosed.comp A.obj B.obj Z.obj = (ihom A.obj).map f := by
    rw [whiskerLeft_curry'_comp, Iso.inv_hom_id_assoc]
  exact congrArg (fun m => m.app n s.val) h

/-- 同じ全空間比較の対角は、元の後合成の後の標準 Hom 比較そのもの。 -/
lemma qCatCoherentCompositionCorrespondence_diagonal (A B Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}) (f : B ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentCompositionCorrespondence A B Z f ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonal (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f) =
      (SSet.uliftFunctor.{u + 1, u}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((ihom A.obj).map (show B.obj ⟶ Z.obj from f))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison A Z := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionCorrespondence_diagonal, ← Category.assoc,
    qCatCoherentCompositionFixedParameter_comp]

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
