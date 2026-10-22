module

public import SerrePositivity.InfinityCategories.F2.Ind.PresheafDensityRestrictedValuePre
public import SerrePositivity.InfinityCategories.F2.Ind.TwistedIdentityFiberEquivalence
public import SerrePositivity.InfinityCategories.F1.UniverseEquivalenceDescent

/-!
概要：元の大域密度評価を恒等点の同じ fiber へ制限した指定値写像は同値。
方針：同じ小さい評価の持ち上げを回収し、恒等点上の元の評価と元の fiber 値比較へ因子分解する。
規約：元の大域切断と元の値写像を変更しない。
使われ方：Yoneda comma 比較の実際の値写像との同じ fiber 上の比較先。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)
local notation "p" => smallRightUnstraighteningProjection F

/-- 同じ大域評価を、元の恒等点上の全 fiber パラメータへ制限した元の指定値写像。 -/
def presheafDensityIdentityValue :=
  (SSet.uliftFunctor.{u + 1, u}).map (twistedSourceElementsIdentityInclusion p x) ≫
    presheafDensityRestrictedGlobalValueMap F x

/-- 同じ指定値写像は、元の恒等点評価と元の fiber 値比較の同じ合成の持ち上げ。 -/
lemma presheafDensityIdentityValue_factorization :
    presheafDensityIdentityValue F x = (SSet.uliftFunctor.{u + 1, u}).map
      (twistedIdentityFiberEvaluation p x ≫ (presheafRightFiberValueEquivalence F x).hom) := by
  rw [presheafDensityIdentityValue, ← presheafDensityRestrictedSmallValueMap_lift,
    ← Functor.map_comp, presheafDensityRestrictedSmallValueMap, ← Category.assoc,
    twistedSourceElementsEvaluation_identity]

/-- 元の恒等点上の同じ大域評価自身は、元の指定値への同値。 -/
lemma presheafDensityIdentityValue_isQCatEquivalence :
    IsQCatEquivalence (presheafDensityIdentityValue F x) := by
  rw [presheafDensityIdentityValue_factorization]
  exact ((twistedIdentityFiberEvaluation_isQCatEquivalence p x).comp
    (presheafRightFiberValueEquivalence F x).isQCatEquivalence).ulift

end SerrePositivity.InfinityCategories.F2.Ind
