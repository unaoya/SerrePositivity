module

public import SerrePositivity.InfinityCategories.F2.Ind.DensityIdentityLift

/-!
概要：元の密度持ち上げの pointed 終値自身の同値性を取り出す。
方針：証明済みの値写像の同値から値比較を消去し、同じ指定値へ表示を正規化する。
規約：元の終値を使い、同値の逆射を選び直さない。
使われ方：同じ始値・同じ区間族の普遍輸送の同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)

/-- 同じ pointed 終値を、元の F の指定対象の値で正規化する。 -/
def presheafDensityIdentityLiftEndpointAtValue :=
  presheafDensityIdentityLiftEndpoint F x ≫
    eqToHom (congrArg (vertexFiber pointedSpaceProjection)
      (presheafDensityEvaluationVertex_value F x))

/-- 元の密度持ち上げの pointed 終値自身が同値。 -/
lemma presheafDensityIdentityLiftEndpoint_isQCatEquivalence :
    IsQCatEquivalence (presheafDensityIdentityLiftEndpoint F x) := by
  have h := (pointedSpaceFiberValueEquivalence
    (presheafDensityEvaluationVertex F x)).isQCatEquivalence
  exact h.cancel_right (presheafDensityIdentityLiftEndpoint_value_isQCatEquivalence F x)

/-- 元の F の指定値で正規化した同じ終値自身が同値。 -/
lemma presheafDensityIdentityLiftEndpointAtValue_isQCatEquivalence :
    IsQCatEquivalence (presheafDensityIdentityLiftEndpointAtValue F x) :=
  (presheafDensityIdentityLiftEndpoint_isQCatEquivalence F x).comp
    (qCatEquivalenceOfIso (eqToIso (congrArg (vertexFiber pointedSpaceProjection)
      (presheafDensityEvaluationVertex_value F x)))).isQCatEquivalence

end SerrePositivity.InfinityCategories.F2.Ind
