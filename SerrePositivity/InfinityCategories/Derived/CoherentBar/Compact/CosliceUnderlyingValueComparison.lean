module
public import SerrePositivity.InfinityCategories.Derived.DGModuleUnderlyingCosliceTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.SpaceEdgeTransportValue
/-!
概要：始点固定 coslice の同じ fiber を、同じ native 基礎空間関手の値へ比較する。
方針：始点固定 Tw の pointed 表示と、既存の全 fiber 同値を合成する。
規約：実際の fiber 射を使い、値の宇宙持ち上げを明示する。
使われ方：線形 Hom の実輸送を native 評価空間の実辺へ照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {C : SSet.{u}} [Quasicategory C] (x y : C _⦋0⦌)

/-- 同じ Yoneda 指定点評価で表した、native 基礎空間関手。 -/
def dgBarCompactUnderlyingValueFunctor :
    (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ SpaceInfinity.{u} :=
  yonedaInfinityMap C ≫ evaluateFunctorAt (ULift.up (SSet.opObjEquiv.symm x))

/-- 同じ coslice から始点固定 Tw への全 fiber 射。 -/
def dgBarCompactCosliceSourceFiberMap :
    vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y ⟶
      vertexFiber (twistedArrowSourceProjection x) y :=
  vertexFiberMap _ _ (cosliceToTwistedArrowSource x)
    (cosliceToTwistedArrowSource_projection x) y

lemma dgBarCompactCosliceSourceFiberMap_isQCatEquivalence :
    IsQCatEquivalence (dgBarCompactCosliceSourceFiberMap x y) :=
  vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence _ _ _ _
    (cosliceToTwistedArrowSource_isPrecompositionEquivalence x) y

/-- 同じ実 coslice fiber から、持ち上げた native 基礎空間値への比較射。 -/
def dgBarCompactCosliceUnderlyingValueComparison :
    (SSet.uliftFunctor.{u + 1, u}).obj
      (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) ⟶
    (SSet.uliftFunctor.{u + 1, u}).obj
      (spaceInfinityObject ((dgBarCompactUnderlyingValueFunctor x).app
        (Opposite.op ⦋0⦌) (ULift.up y))).obj :=
  (SSet.uliftFunctor.{u + 1, u}).map (dgBarCompactCosliceSourceFiberMap x y) ≫
    (uliftVertexFiberIso.{u, u + 1} (twistedArrowSourceProjection x) y).hom ≫
      twistedArrowSourcePointedDisplayFiber x y ≫
        (pointedSpaceFiberValueEquivalence
          ((dgBarCompactUnderlyingValueFunctor x).app (Opposite.op ⦋0⦌) (ULift.up y))).hom

lemma dgBarCompactCosliceUnderlyingValueComparison_isQCatEquivalence :
    IsQCatEquivalence (dgBarCompactCosliceUnderlyingValueComparison x y) := by
  have h₁ := (dgBarCompactCosliceSourceFiberMap_isQCatEquivalence x y).ulift.{u, u + 1}
  have h₂ := (qCatEquivalenceOfIso
    (uliftVertexFiberIso.{u, u + 1} (twistedArrowSourceProjection x) y)).isQCatEquivalence
  have h₃ := twistedArrowSourcePointedDisplayFiber_isQCatEquivalence x y
  have h₄ := (pointedSpaceFiberValueEquivalence
    ((dgBarCompactUnderlyingValueFunctor x).app (Opposite.op ⦋0⦌) (ULift.up y))).isQCatEquivalence
  exact h₁.comp (h₂.comp (h₃.comp h₄))

end SerrePositivity.InfinityCategories
