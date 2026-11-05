module
public import SerrePositivity.InfinityCategories.Derived.DGCosliceYonedaPointedDisplay
public import SerrePositivity.InfinityCategories.Derived.DGHomTargetTransportRepresentation
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallStraighteningCounit
/-!
概要：同じ Hom 単位による空間値全関手を、元の F1 Yoneda 指定点評価と比較する。
方針：同じ実 coslice を表す二つの transport 表現を同じ可縮空間内で比較する。
規約：一つの全比較証人で分類図式と pointed 全空間の両方を比較する。
使われ方：D(R) 値 Hom と元の F1 Hom 関手族の全関手同型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C] (x : C)
/-- 同じ実 coslice の二表現を、同じ可縮な表現空間内で比較する実証人。 -/
def dgHomTargetSpaceComparisonWitness :
    VertexIso (transportWitnessVertex (dgHomTargetTransportRepresentation R C x))
      (transportWitnessVertex (dgCosliceYonedaTransportRepresentation
        (dgNerve R C) (Simplex.vertex x))) := by
  have (n : SimplexCategoryᵒᵖ) : Small.{max (u + 1) v}
      (((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
        (sliceUnder ((SSet.yonedaEquiv (X := dgNerve R C)).symm (Simplex.vertex x)))).obj n) :=
    inferInstanceAs (Small.{max (u + 1) v} (ULift.{max (u + 1) v + 1}
      ((sliceUnder ((SSet.yonedaEquiv (X := dgNerve R C)).symm (Simplex.vertex x))).obj n)))
  exact smallTransportRepresentationVertexIso.{max (u + 1) v} _
    (dgHomTargetTransportRepresentation R C x)
    (dgCosliceYonedaTransportRepresentation (dgNerve R C) (Simplex.vertex x))
/-- 同じ比較証人から作る、Hom 基礎空間全関手と元の F1 Yoneda 評価の全関手同型。 -/
def dgHomTargetSpaceComparisonIso :
    FunctorIso (dgHomTargetUnderlyingSpaceInfinity R C x)
      (dgCosliceYonedaSpaceInfinity (dgNerve R C) (Simplex.vertex x)) :=
  (dgHomTargetTransportRepresentation R C x).diagramIso
    (dgCosliceYonedaTransportRepresentation (dgNerve R C) (Simplex.vertex x))
    (dgHomTargetSpaceComparisonWitness R C x)
/-- 同じ比較証人から作る、二つの実 pointed 全空間写像の全関手同型。 -/
def dgHomTargetPointedComparisonIso :
    FunctorIso (dgHomTargetCoslicePointedDisplay R C x)
      (dgCosliceYonedaPointedDisplay (dgNerve R C) (Simplex.vertex x)) := by
  have e := (dgHomTargetTransportRepresentation R C x).pointedIso
    (dgCosliceYonedaTransportRepresentation (dgNerve R C) (Simplex.vertex x))
    (dgHomTargetSpaceComparisonWitness R C x)
  simpa only [dgHomTargetTransportRepresentation_pointedMap,
    dgCosliceYonedaTransportRepresentation, dgPointedTransportRepresentation_pointedMap] using e
end SerrePositivity.InfinityCategories
