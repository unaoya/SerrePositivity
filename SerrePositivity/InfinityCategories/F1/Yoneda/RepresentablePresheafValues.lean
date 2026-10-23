module

public import SerrePositivity.InfinityCategories.F1.Yoneda.RepresentableUnstraighteningComparison
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraighteningFiber
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationFiberReflection
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseLeftFilling
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseRightFilling
public import SerrePositivity.InfinityCategories.Core.PinchedSlice

/-!
概要：同じ Yoneda 対象前層の値を、元の quasicategory の標準写像空間と比較する。
方針：元の表現可能射影の fiber、反転、実際の unstraightening 比較の fiber を順に通る。
規約：Kan 複体の反転は edgewise 解像の両射影による同値で戻し、厳密な同型とは主張しない。
使われ方：Yoneda 評価の F=rep(z) への特殊化と、元の Hom 作用の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- Kan 複体の反転を、共通 edgewise 解像の両端射影で元の Kan 複体へ比較する。 -/
def kanOppositeEdgewiseEquivalence (K : SSet.{u}) [KanComplex K] :
    QCatEquivalence K.op K :=
  (isQCatEquivalence_of_trivialKanFibration (edgewiseLeft K)).choose.symm.trans
    (isQCatEquivalence_of_trivialKanFibration (edgewiseRight K)).choose

/-- 同じ表現可能前層の値と、元の右 slice fiber の反転との比較。 -/
def representablePresheafOppositeHomValueEquivalence
    {C : SSet.{u}} [Quasicategory C] (x y : C _⦋0⦌) :
    QCatEquivalence (pinchedHom x y).op
      (spaceInfinityObject ((representablePresheafInfinity y).app (Opposite.op ⦋0⦌)
        (ULift.up (SSet.opObjEquiv.symm x)))).obj := by
  let e₁ := SSet.opFunctor.mapIso (pinchedHomSliceFiberIso x y)
  let e₂ := HomotopyLimits.oppositeVertexFiberIso
    (sliceOverProjection (SSet.yonedaEquiv.symm y)) x
  have h := vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence
    (SSet.opFunctor.map (sliceOverProjection (SSet.yonedaEquiv.symm y)))
    (smallLeftUnstraighteningProjection (representablePresheafInfinity y))
    (representableLeftUnstraighteningComparison y)
    (representableLeftUnstraighteningComparison_projection y)
    (representableLeftUnstraighteningComparison_isPrecompositionEquivalence y)
    (SSet.opObjEquiv.symm x)
  exact (qCatEquivalenceOfIso e₁).trans ((qCatEquivalenceOfIso e₂).trans
    (h.choose.trans (smallLeftUnstraighteningFiberValueEquivalence
      (representablePresheafInfinity y) (SSet.opObjEquiv.symm x))))

/-- 同じ Yoneda 前層の指定対象での値は、元の quasicategory の標準写像空間と同値。 -/
def representablePresheafValueEquivalence
    {C : SSet.{u}} [Quasicategory C] (x y : C _⦋0⦌) :
    QCatEquivalence
      (spaceInfinityObject ((representablePresheafInfinity y).app (Opposite.op ⦋0⦌)
        (ULift.up (SSet.opObjEquiv.symm x)))).obj (pinchedHom x y) :=
  (representablePresheafOppositeHomValueEquivalence x y).symm.trans
    (kanOppositeEdgewiseEquivalence (pinchedHom x y))

end SerrePositivity.InfinityCategories
