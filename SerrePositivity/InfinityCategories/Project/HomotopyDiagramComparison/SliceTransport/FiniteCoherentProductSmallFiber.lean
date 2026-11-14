module
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.FiniteKanProductComparison

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CoherentDiagrams.FiniteCoherentProductTotalMap
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.CoherentProductSmallFiber

/-!
概要：元の有限 coherent 積の小さい全空間射影の対は、各頂点 fiber で同値。
方針：元の全射影の fiber 射を反復積へまとめ、二項比較との厳密な因子化で帰納する。
規約：底の quasicategory 性は不要。元の全射影の作用を保持する。
使われ方：有限 coherent 積の指定全空間比較の同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensor_isKan

/-- 元の全空間射影を小さい頂点 fiber に制限して組にする。 -/
def finiteCoherentProductSmallFiberMap (n : ℕ) {B : SSet.{u}}
    (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))
    (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F)) b ⟶
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProduct n (fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection
        (F i)) b) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetLift n (fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap _ _
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProductTotalProjection n F i)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProductTotalProjection_base n F i) b)

/-- 元の有限 fiber 比較の各成分は、元の全空間射影の fiber 射。 -/
lemma finiteCoherentProductSmallFiberMap_projection (n : ℕ) {B : SSet.{u}}
    (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))
    (b : B _⦋0⦌) (i : Fin (n + 1)) : finiteCoherentProductSmallFiberMap n F b ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProjection n (fun j ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (F j)) b) i =
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap _ _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProductTotalProjection n F i)
            (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProductTotalProjection_base n F i) b :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetLift_projection _ _ _

/-- 元の有限 fiber 比較は、元の二項比較と tail 比較の積に厳密に因子化する。 -/
lemma finiteCoherentProductSmallFiberMap_succ (n : ℕ) {B : SSet.{u}}
    (F : Fin (n + 1 + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))
    (b : B _⦋0⦌) : finiteCoherentProductSmallFiberMap (n + 1) F b =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentProductSmallFiberMap (F 0)
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n (fun i ↦ F i.succ)) b ≫
          (𝟙 _ ⊗ₘ finiteCoherentProductSmallFiberMap n (fun i ↦ F i.succ) b) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProduct_hom_ext (n + 1) _
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rw [finiteCoherentProductSmallFiberMap_projection, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProjection,
      Fin.cases_zero, Category.assoc, tensorHom_fst, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentProductSmallFiberMap, lift_fst, Category.comp_id]
    rfl
  · rw [finiteCoherentProductSmallFiberMap_projection, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProjection,
      Fin.cases_succ, ← Category.assoc, Category.assoc _ _ (snd _ _), tensorHom_snd,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentProductSmallFiberMap, lift_snd, Category.assoc,
      finiteCoherentProductSmallFiberMap_projection, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_comp]
    rfl

local instance (n : ℕ) {B : SSet.{u}}
    (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))
    (b : B _⦋0⦌) : KanComplex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProduct n
      (fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (F i)) b)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProduct_kanComplex n _ (fun _ ↦ inferInstance)

/-- 任意の小さい底上で、元の有限全射影の fiber 比較は同値。 -/
lemma finiteCoherentProductSmallFiberMap_isQCatEquivalence (n : ℕ) {B : SSet.{u}}
    (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))
    (b : B _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (finiteCoherentProductSmallFiberMap n F b) := by
  induction n with
  | zero =>
    have h : finiteCoherentProductSmallFiberMap 0 F b = 𝟙 _ := by
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_id _ _
    rw [h]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (Iso.refl _)).isQCatEquivalence
  | succ n ih =>
    rw [finiteCoherentProductSmallFiberMap_succ]
    exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentProductSmallFiberMap_isQCatEquivalence (F 0) _ b).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.tensor_isQCatEquivalence
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (Iso.refl _)).isQCatEquivalence (ih _))

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
