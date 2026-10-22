module

public import SerrePositivity.InfinityCategories.F2.Ind.PresheafRightFiberPointedIso
public import SerrePositivity.InfinityCategories.F2.Ind.PresheafDensityEvaluationValueComparison
public import SerrePositivity.InfinityCategories.F2.Ind.TwistedSourceElementsWeakEquivalence

/-!
概要：元の制限大域評価の値写像を、同じ始点固定評価と元の fiber 比較の合成へ同定する。
方針：pointed fiber の包含後に、元の大域評価の全空間成分を比較する。
規約：構成済みの同じ評価写像を用い、同値な別の射へ置き換えない。
使われ方：証明済みの始点固定評価の弱同値を密度の実際の値写像へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)
local notation "p" => smallRightUnstraighteningProjection F
local notation "z" => presheafDensityEvaluationVertex F x

/-- 元の制限大域評価の pointed fiber 写像は、同じ始点固定評価の持ち上げそのもの。 -/
lemma presheafDensityRestrictedGlobalMap_pointedFactorization :
    presheafDensityRestrictedGlobalMap F x ≫
      F2.constantUnstraighteningFiberProjection
        ((SSet.uliftFunctor.{u + 1, u}).obj (smallRightUnstraightening F)) z =
    (SSet.uliftFunctor.{u + 1, u}).map (twistedSourceElementsEvaluation p x) ≫
      (presheafRightFiberPointedIso F x).hom := by
  apply vertexFiber_hom_ext pointedSpaceProjection z
  rw [Category.assoc, F2.constantUnstraighteningFiberProjection, Category.assoc,
    constantPullbackFiberIso_fst_ι]
  rw [presheafDensityRestrictedGlobalMap, pullback.lift_fst, Category.assoc,
    presheafRightFiberPointedIso_ι]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc
    ((SSet.uliftFunctor.{u + 1, u}).map (twistedSourceElementsEvaluation p x)),
    ← Functor.map_comp, twistedSourceElementsEvaluation_ι]
  simp only [presheafTwistedElementsEvaluation, twistedSourceElementsSourceMap,
    Functor.map_comp, Category.assoc]

/-- 同じ元の値写像は、同じ始点固定評価と元の pointed fiber 値比較の合成。 -/
lemma presheafDensityRestrictedGlobalValueMap_factorization :
    presheafDensityRestrictedGlobalValueMap F x =
      (SSet.uliftFunctor.{u + 1, u}).map (twistedSourceElementsEvaluation p x) ≫
        (presheafRightFiberPointedIso F x).hom ≫ (pointedSpaceFiberValueEquivalence z).hom := by
  rw [presheafDensityRestrictedGlobalValueMap, ← Category.assoc,
    presheafDensityRestrictedGlobalMap_pointedFactorization, Category.assoc]

end SerrePositivity.InfinityCategories.F2.Ind
