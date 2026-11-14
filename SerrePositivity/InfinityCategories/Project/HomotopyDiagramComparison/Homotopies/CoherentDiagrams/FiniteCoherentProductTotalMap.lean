module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.SpaceTensorProductTotalMap
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.FiniteCommonFiberProductUniversal

/-!
概要：有限 coherent 積の元の小さい全空間から、元の有限共通 fiber 積への比較。
方針：元の二項積の全空間射影を反復し、元の全成分から普遍射を構成する。
規約：元の全空間・底射影・各成分を保持。比較の同値性は別工程。
使われ方：有限 sifted 積比較を元の coherent 余極限頂点へ移すための指定射。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の n+1 個の coherent 空間値図式の点ごとの反復積。 -/
def finiteCoherentSpaceProduct {B : SSet.{u + 1}} : (n : ℕ) →
    (Fin (n + 1) → (B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})) → (B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  | 0, F => F 0
  | n + 1, F => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProduct (F 0)
      (finiteCoherentSpaceProduct n (fun i ↦ F i.succ))

/-- 元の二項射影の全空間作用を反復した、元の各図式への全空間射影。 -/
def finiteCoherentSpaceProductTotalProjection {B : SSet.{u}} : (n : ℕ) →
    (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})) →
    (i : Fin (n + 1)) → (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening (finiteCoherentSpaceProduct n F) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening (F i))
  | 0, F, i => eqToHom
      (congrArg (fun j ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening (F j)) (Fin.eq_zero i).symm)
  | n + 1, F, i => Fin.cases
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductTotalFst (F 0)
        (finiteCoherentSpaceProduct n (fun j ↦ F j.succ)))
      (fun j ↦ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductTotalSnd (F 0)
        (finiteCoherentSpaceProduct n (fun k ↦ F k.succ)) ≫
          finiteCoherentSpaceProductTotalProjection n (fun k ↦ F k.succ) j) i

/-- 各元の全空間射影は同じ元の底射影を厳密に被覆する。 -/
lemma finiteCoherentSpaceProductTotalProjection_base (n : ℕ) {B : SSet.{u}}
    (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))
    (i : Fin (n + 1)) : finiteCoherentSpaceProductTotalProjection n F i ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (F i) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (finiteCoherentSpaceProduct n F) := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp only [finiteCoherentSpaceProductTotalProjection, eqToHom_refl,
      Category.id_comp, finiteCoherentSpaceProduct]
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap_projection _ _ _
    · change (_ ≫ _) ≫ _ = _
      rw [Category.assoc, ih]
      exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap_projection _ _ _

/-- 元の有限 coherent 積の小さい全空間から、元の有限共通 fiber 積への指定比較。 -/
def finiteCoherentSpaceProductTotalComparison (n : ℕ) {B : SSet.{u}}
    (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening (finiteCoherentSpaceProduct n F) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteCommonFiberProduct n (fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (F i)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCommonFiberProductLift n (fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (F i))
    (finiteCoherentSpaceProductTotalProjection n F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (finiteCoherentSpaceProduct n F))
    (finiteCoherentSpaceProductTotalProjection_base n F)

/-- 元の比較の全成分は、同じ二項射影を反復した元の全空間射影。 -/
lemma finiteCoherentSpaceProductTotalComparison_projection (n : ℕ) {B : SSet.{u}}
    (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))
    (i : Fin (n + 1)) : finiteCoherentSpaceProductTotalComparison n F ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteCommonFiberProductProjection n
        (fun j ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (F j)) i =
          finiteCoherentSpaceProductTotalProjection n F i :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCommonFiberProductLift_projection _ _ _ _ _ _

/-- 元の有限比較は元の小さい全空間の底射影を厳密に保持する。 -/
lemma finiteCoherentSpaceProductTotalComparison_base (n : ℕ) {B : SSet.{u}}
    (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})) :
    finiteCoherentSpaceProductTotalComparison n F ≫
      pullback.snd (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProductMap n
        (fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (F i))) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.nonemptyFiniteDiagonal B n) =
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (finiteCoherentSpaceProduct n F) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCommonFiberProductLift_base _ _ _ _ _

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
