module
public import SerrePositivity.InfinityCategories.Derived.DGPointedTransportRepresentation
public import SerrePositivity.InfinityCategories.Derived.DGHomTargetPointedFiberEquivalence
/-!
概要：同じ Hom 単位の実 pointed 表示を、元の coslice 射影の実 transport 表現にする。
方針：構成済みの全実 fiber 同値を用い、同じ全関手・同じ全空間写像を保持する。
規約：入力の小ささも出力の射影性も不要。使われ方：F1 Hom 関手族との全分類比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C] (x : C)
/-- 同じ実 Hom 単位の全単体表示から作る、元の coslice の実 transport 表現。 -/
def dgHomTargetTransportRepresentation :
    LeftTransportRepresentation ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
      (sliceUnderProjection ((SSet.yonedaEquiv (X := dgNerve R C)).symm (Simplex.vertex x)))) :=
  dgPointedTransportRepresentation _ (dgHomTargetUnderlyingSpaceInfinity R C x)
    (dgHomTargetCoslicePointedDisplay R C x) (dgHomTargetCoslicePointedDisplay_projection R C x) (by
      rintro ⟨b⟩
      exact dgHomTargetCoslicePointedDisplay_fiber_isQCatEquivalence R C x b)
/-- 同じ実表現の分類図式は、元の同じ Hom 基礎空間関手。 -/
lemma dgHomTargetTransportRepresentation_diagram :
    (dgHomTargetTransportRepresentation R C x).diagram =
      dgHomTargetUnderlyingSpaceInfinity R C x := rfl
/-- 同じ実表現の全空間側の写像は、元の同じ Hom 単位の pointed 表示。 -/
lemma dgHomTargetTransportRepresentation_pointedMap :
    (dgHomTargetTransportRepresentation R C x).pointedMap =
      dgHomTargetCoslicePointedDisplay R C x := by
  exact dgPointedTransportRepresentation_pointedMap _ _ _ _ _
end SerrePositivity.InfinityCategories
