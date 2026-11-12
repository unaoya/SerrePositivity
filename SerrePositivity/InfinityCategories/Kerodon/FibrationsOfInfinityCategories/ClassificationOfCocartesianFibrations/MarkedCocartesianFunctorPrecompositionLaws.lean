module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.MarkedCocartesianFunctorPrecomposition

/-!
概要：指定辺を保つ相対 Hom の前合成の恒等・合成則。
方針：元の全部分複体への包含で反映し、全相対 Hom の厳密な前合成則を使う。
規約：始域・標的の充填性を仮定しない。
使われ方：各底変換上の cocartesian Hom の実際の制限図式。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 指定辺を保つ恒等射による前合成は、元の相対 Hom の恒等射。 -/
lemma markedCocartesianFunctorPre_id {E B : SSet.{u}} (q : E ⟶ B) (a : Over B)
    (W : Set (a.left _⦋1⦌))
    (h : ∀ e ∈ W, (𝟙 a : a ⟶ a).left.app (Opposite.op ⦋1⦌) e ∈ W) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre q (𝟙 a) W W h = 𝟙 _ := by
  apply (cancel_mono
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate q a.hom W)).ι).mp
  change _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorInclusion q a.hom W =
    _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorInclusion q a.hom W
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre_id,
    Category.comp_id, Category.id_comp]

/-- 指定辺を保つ射の合成による前合成は、元の全高次の前合成の合成。 -/
lemma markedCocartesianFunctorPre_comp {E B : SSet.{u}} (q : E ⟶ B)
    {a b c : Over B} (i : a ⟶ b) (j : b ⟶ c)
    (U : Set (a.left _⦋1⦌)) (V : Set (b.left _⦋1⦌)) (W : Set (c.left _⦋1⦌))
    (hi : ∀ e ∈ U, i.left.app (Opposite.op ⦋1⦌) e ∈ V)
    (hj : ∀ e ∈ V, j.left.app (Opposite.op ⦋1⦌) e ∈ W)
    (hij : ∀ e ∈ U, (i ≫ j).left.app (Opposite.op ⦋1⦌) e ∈ W) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre q (i ≫ j) U W hij =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre q j V W hj ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre q i U V hi := by
  apply (cancel_mono
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate q a.hom U)).ι).mp
  change _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorInclusion q a.hom U =
    _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorInclusion q a.hom U
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre_ι, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre_ι,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre_ι, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre_comp]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
