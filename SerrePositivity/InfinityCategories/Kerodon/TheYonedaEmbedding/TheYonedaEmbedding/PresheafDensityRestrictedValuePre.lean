module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafDensityRestrictedValueFactorization
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafRightFiberValue
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.UliftPrecomposition

/-!
概要：元の制限大域評価の値写像は、小さい Kan 標的の持ち上げへの前合成同値を与える。
方針：同じ値写像を元の宇宙へ降ろし、証明済みの始点固定評価の弱同値を使う。
規約：任意の大きい標的への弱同値を仮定せず、必要な標的の宇宙を明示する。
使われ方：密度の実際の評価 fiber 写像の余極限判定。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (x : C _⦋0⦌)
local notation "p" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraighteningProjection F

/-- 元の制限大域評価の値写像と同じ順方向の射を、元の宇宙で表す。 -/
def presheafDensityRestrictedSmallValueMap :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElementsEvaluation p x ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafRightFiberValueEquivalence F x).hom

/-- 同じ小さい値写像の持ち上げは、元の制限大域評価の同じ値写像そのもの。 -/
lemma presheafDensityRestrictedSmallValueMap_lift :
    (SSet.uliftFunctor.{u + 1, u}).map (presheafDensityRestrictedSmallValueMap F x) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityRestrictedGlobalValueMap F x := by
  rw [presheafDensityRestrictedSmallValueMap, Functor.map_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafRightFiberValueEquivalence_lift, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityRestrictedGlobalValueMap_factorization]

/-- 同じ小さい値写像は、元の始点固定評価の弱同値性を保つ。 -/
lemma presheafDensityRestrictedSmallValueMap_isWeakHomotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (presheafDensityRestrictedSmallValueMap F x) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElementsEvaluation_isWeakHomotopyEquivalence p x).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsPrecompositionEquivalence.isWeakHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafRightFiberValueEquivalence F x).isQCatEquivalence.isPrecompositionEquivalence)

/-- 元の同じ値写像は、小さい Kan 標的の持ち上げへの前合成のホモトピー同値を与える。 -/
lemma presheafDensityRestrictedGlobalValueMap_pre (Z : SSet.{u}) [KanComplex Z] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityRestrictedGlobalValueMap F x)).app
        ((SSet.uliftFunctor.{u + 1, u}).obj Z)) := by
  rw [← presheafDensityRestrictedSmallValueMap_lift]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ulift_pre_homotopyEquivalence _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.pre_isSimplicialHomotopyEquivalence_of_weakHomotopyEquivalence _
      (presheafDensityRestrictedSmallValueMap_isWeakHomotopyEquivalence F x) Z)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
