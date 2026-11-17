module

public import SerrePositivity.AlgebraicGeometry.ArcRouteB.PerfectedFpArc
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.PerfectedModelColimit
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.FilteredUniversalCech
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.LocalExtensions
public import SerrePositivity.CommutativeAlgebra.ValuationInterval.Zorn
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalTensorComparison
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalRestrictions
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.BaseChangeComparison
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.BaseChangeArrowComparison
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalCoefficientPerfect
public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Milnor.ArcCechMilnor

/-!
概要：絶対整閉な完全付値環上の任意のarc被覆の普遍Čech完全性。
方針：同じ有限表示模型の完全化へI11を適用し、指定余錐の余極限で戻す。
規約：模型の付け替えやNoether仮定を加えない。
使われ方：2iのI12、BM18 Proposition 4.8(1)の完結。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity
open SerrePositivity.BhattScholze.Perfectoidization
open scoped TensorProduct
namespace SerrePositivity.AlgebraicGeometry.ArcRouteB

set_option backward.isDefEq.respectTransparency false

/-- 計画I12：同じ完全化模型の余極限により、絶対整閉付値環上のarc被覆を扱う。 -/
theorem aicValuationArc_universalExact (p : ℕ) [Fact p.Prime]
    {V B : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [CommRing B]
    [PerfectRing V p] [PerfectRing B p] (hV : IsAbsolutelyIntegrallyClosed V)
    (hp : (p : V) = 0) (f : V →+* B) (hf : IsArcHom f) :
    PerfectRingCechUniversalExact p f := by
  letI := f.toAlgebra
  apply perfectRingCechUniversalExact_of_filtered_models p
    (perfectedModelDiagram p V B hp) (perfectedModelCocone p V B hp)
    (perfectedModelCoconeIsColimit p V B hp)
  intro j
  let X := (equivSmallModel (FinitePresentationModelCategory V B)).inverse.obj j
  let C := X.obj.left.obj
  have hc := perfectedModel_isArcHom p hp hf j
  have h := perfectedFpArc_universalExact p (V := V) (C := C) hV hp
  apply h
  exact hc

end SerrePositivity.AlgebraicGeometry.ArcRouteB
