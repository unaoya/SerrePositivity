module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafDensityRestrictedValueFactorization
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafRightFiberValue
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.UliftPrecomposition

/-!
概要：元の制限大域評価の値写像は、小さい Kan 標的の持ち上げへの前合成同値を与える。
方針：同じ値写像を元の宇宙へ降ろし、証明済みの始点固定評価の弱同値を使う。
規約：任意の大きい標的への弱同値を仮定せず、必要な標的の宇宙を明示する。
使われ方：密度の実際の評価 fiber 写像の余極限判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)
local notation "p" => smallRightUnstraighteningProjection F

/-- 元の制限大域評価の値写像と同じ順方向の射を、元の宇宙で表す。 -/
def presheafDensityRestrictedSmallValueMap :=
  twistedSourceElementsEvaluation p x ≫ (presheafRightFiberValueEquivalence F x).hom

/-- 同じ小さい値写像の持ち上げは、元の制限大域評価の同じ値写像そのもの。 -/
lemma presheafDensityRestrictedSmallValueMap_lift :
    (SSet.uliftFunctor.{u + 1, u}).map (presheafDensityRestrictedSmallValueMap F x) =
      presheafDensityRestrictedGlobalValueMap F x := by
  rw [presheafDensityRestrictedSmallValueMap, Functor.map_comp,
    presheafRightFiberValueEquivalence_lift, presheafDensityRestrictedGlobalValueMap_factorization]

/-- 同じ小さい値写像は、元の始点固定評価の弱同値性を保つ。 -/
lemma presheafDensityRestrictedSmallValueMap_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence (presheafDensityRestrictedSmallValueMap F x) :=
  (twistedSourceElementsEvaluation_isWeakHomotopyEquivalence p x).comp
    (IsPrecompositionEquivalence.isWeakHomotopyEquivalence
      (presheafRightFiberValueEquivalence F x).isQCatEquivalence.isPrecompositionEquivalence)

/-- 元の同じ値写像は、小さい Kan 標的の持ち上げへの前合成のホモトピー同値を与える。 -/
lemma presheafDensityRestrictedGlobalValueMap_pre (Z : SSet.{u}) [KanComplex Z] :
    IsSimplicialHomotopyEquivalence
      ((pre (presheafDensityRestrictedGlobalValueMap F x)).app
        ((SSet.uliftFunctor.{u + 1, u}).obj Z)) := by
  rw [← presheafDensityRestrictedSmallValueMap_lift]
  exact F2.ulift_pre_homotopyEquivalence _
    (pre_isSimplicialHomotopyEquivalence_of_weakHomotopyEquivalence _
      (presheafDensityRestrictedSmallValueMap_isWeakHomotopyEquivalence F x) Z)

end SerrePositivity.InfinityCategories.F2.Ind
