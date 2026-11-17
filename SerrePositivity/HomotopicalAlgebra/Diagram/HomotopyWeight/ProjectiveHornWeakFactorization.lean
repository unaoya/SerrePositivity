module
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ProjectiveHornFactorization
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanSourceReplacement
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakWhitehead
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.KanFibrationEquivalence

/-!
概要：各値がKanな標的への重みの弱同値の自由ホーン分解は、各値で境界の右類を持つ。
方針：左射のanodyne性、弱同値の二対三則、Kan Whiteheadと既存の相対充填を使う。
規約：IS-W2 R03a.1の証明分割。一般の非Kan標的の場合をこの補題で代用しない。
使われ方：重みのホーン置換後に元の右射の切断とホモトピーを得る。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SSet _root_.HomotopicalAlgebra
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open scoped _root_.SSet.modelCategoryQuillen
variable (I : Type u) [SmallCategory I]

/-- 同じ分解の左射は、元の各値で弱ホモトピー同値。 -/
theorem projectiveHornFactorization_i_weak {V W : I ⥤ SSet.{u}} (j : V ⟶ W) (i : I) :
    IsWeakHomotopyEquivalence ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.projectiveHornFactorization I j).i.app i) := by
  intro Z hZ
  exact (homotopyEquivalence_pre_of_anodyne _
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.projectiveHornFactorization_i_anodyne I j i) Z).mapPiZero_bijective

/-- 同じ元の弱同値の分解の右射も、各値で弱ホモトピー同値。 -/
theorem projectiveHornFactorization_p_weak {V W : I ⥤ SSet.{u}} (j : V ⟶ W)
    (hj : ∀ i, IsWeakHomotopyEquivalence (j.app i)) (i : I) :
    IsWeakHomotopyEquivalence ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.projectiveHornFactorization I j).p.app i) := by
  apply (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.projectiveHornFactorization_i_weak I j i).cancel_left
  have h := NatTrans.congr_app (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.projectiveHornFactorization I j).fac i
  change (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.projectiveHornFactorization I j).i.app i ≫
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.projectiveHornFactorization I j).p.app i = j.app i at h
  rw [h]
  exact hj i

/-- Kanな元の標的への弱同値の分解の右射は、各値で境界に対して右持ち上げ性。 -/
theorem projectiveHornFactorization_p_boundary_rlp {V W : I ⥤ SSet.{u}} (j : V ⟶ W)
    (hj : ∀ i, IsWeakHomotopyEquivalence (j.app i))
    (hW : ∀ i, SSet.KanComplex (W.obj i)) (i : I) :
    SSet.modelCategoryQuillen.I.rlp ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.projectiveHornFactorization I j).p.app i) := by
  let p := (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.projectiveHornFactorization I j).p.app i
  letI targetKan := hW i
  letI pFibration := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.projectiveHornFactorization_p_fibration I j i
  letI sourceKan := isFibrant_of_fibration p
  have hp := (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.projectiveHornFactorization_p_weak I j hj i).isSimplicialHomotopyEquivalence
  have ht := trivialKanFibration_of_fibration_of_simplicialHomotopyEquivalence p hp
  intro A B f hf
  rcases hf with ⟨n⟩
  exact (trivialKanFibration_iff_boundary p).mp ht n

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
