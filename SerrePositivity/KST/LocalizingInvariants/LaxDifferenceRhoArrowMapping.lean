module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceRhoTargetMapping
public import SerrePositivity.KST.LocalizingInvariants.TensorHomotopyEquivalence
public import SerrePositivity.KST.LocalizingInvariants.KanFibrationEquivalenceBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackMappingProductSquare
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanTensorComplex

/-!
概要：ρ(y) への写像空間の元の lax 矢印関手による比較は同値。
方針：C・D 二辺の積の同値を、元の端点評価の Kan fibration に沿って引き戻す。
規約：元の pinchedHomMap と正方形を保持。使われ方：Tamme Prop. 11 の cofiber 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
local instance rhoArrowMappingTensorKan (A B : SSet.{u}) [KanComplex A] [KanComplex B] :
    KanComplex (A ⊗ B) := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.kanComplex_tensor A B

variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (v : E.obj ⟶ D.obj) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction q.hom v) (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful v)

include a hv in
lemma laxDifferenceRho_arrowMapping_equivalence (x : (laxCategory p q).obj _⦋0⦌)
    (y : E.obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p.hom q.hom) x
      ((laxDifferenceRho p q v).app (Opposite.op ⦋0⦌) y)) := by
  have : Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackMappingEndpointMap p.hom q.hom x
      ((laxDifferenceRho p q v).app (Opposite.op ⦋0⦌) y)) := inferInstance
  apply kanPullback_first_equivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackMappingProduct_isPullback p.hom q.hom x
      ((laxDifferenceRho p q v).app (Opposite.op ⦋0⦌) y))
  exact tensor_simplicialHomotopyEquivalence
    (laxDifferenceRho_fstMapping_equivalence p q v x y)
    (laxDifferenceRho_sndMapping_equivalence p q v a hv x y)

end SerrePositivity.KST.LocalizingInvariants

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite Tamme "Eq (7)"] _root_.SerrePositivity.KST.LocalizingInvariants.laxDifferenceRho_arrowMapping_equivalence
