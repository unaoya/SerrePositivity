module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonDerivedLift
public import SerrePositivity.DifferentialGraded.Verdier.TriangulatedHomComparison
public import Mathlib.CategoryTheory.Localization.Triangulated

/-! # 局所 K-flat 版の実際の導来延長の Verdier 因子化の充満忠実性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance derivedQuotientLiftLifting (S : Set D) :
    Localization.Lifting (triaQuotient A D S) (triaImage A D S).trW
      (derivedComparisonFromTria A D S) (derivedQuotientLift A D S) :=
  Localization.liftingLift (derivedComparisonFromTria A D S)
    (derivedComparisonFromTria_inverts A D S) (triaQuotient A D S)

instance derivedQuotientLiftCommShift (S : Set D) :
    (derivedQuotientLift A D S).CommShift ℤ :=
  Functor.commShiftOfLocalization (triaQuotient A D S) (triaImage A D S).trW ℤ
    (derivedComparisonFromTria A D S) (derivedQuotientLift A D S)

instance derivedQuotientLiftFactorsCommShift (S : Set D) :
    NatTrans.CommShift (derivedQuotientLiftFactors A D S).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization (triaQuotient A D S) (triaImage A D S).trW ℤ
    (derivedComparisonFromTria A D S) (derivedQuotientLift A D S)

instance derivedQuotientLiftIsTriangulated (S : Set D) :
    (derivedQuotientLift A D S).IsTriangulated := by
  have : (triaQuotient A D S).mapArrow.EssSurj :=
    Localization.essSurj_mapArrow (triaQuotient A D S) (triaImage A D S).trW
  exact Functor.isTriangulated_of_precomp_iso (derivedQuotientLiftFactors A D S)

lemma derivedQuotientLift_representable_target (S : Set D) (h : localKFlat A D S) (z : D) :
    homComparisonTarget (derivedQuotientLift A D S)
      ((triaQuotient A D S).obj (triaRepresentable A D z)) := by
  intro X
  let Q := triaQuotient A D S
  exact homComparison_bijective_of_iso (derivedQuotientLift A D S)
    (Q.objObjPreimageIso X) (Iso.refl _)
    (derivedQuotientLift_map_bijective_representable A D S h z (Q.objPreimage X))

/-- 任意の始域から、代表対象の任意の整数 shift への射写像も全単射。 -/
lemma derivedQuotientLift_shifted_representable_target
    (S : Set D) (h : localKFlat A D S) (z : D) (n : ℤ) :
    homComparisonTarget (derivedQuotientLift A D S)
      (((triaQuotient A D S).obj (triaRepresentable A D z))⟦n⟧) :=
  (homComparisonTarget (derivedQuotientLift A D S)).le_shift n _
    (derivedQuotientLift_representable_target A D S h z)

/-- 終域に関する三角閉性と代表生成性により、全ての tria 対象間で全単射になる。 -/
lemma derivedQuotientLift_map_bijective (S : Set D) (h : localKFlat A D S)
    (X Y : TriaQuotient A D S) :
    Function.Bijective ((derivedQuotientLift A D S).map (X := X) (Y := Y)) := by
  let P := homComparisonTarget (derivedQuotientLift A D S)
  let : P.IsTriangulated := homComparisonTargetIsTriangulated _
  have hle : triaImage A D Set.univ ≤ P.inverseImage (triaQuotient A D S) :=
    (triaImage_le_iff_generators A D Set.univ (P.inverseImage (triaQuotient A D S))).2
      (fun z _ => derivedQuotientLift_representable_target A D S h z)
  let Q := triaQuotient A D S
  have hY : P (Q.obj (Q.objPreimage Y)) :=
    hle (Q.objPreimage Y) (Q.objPreimage Y).property
  exact P.prop_of_iso (Q.objObjPreimageIso Y) hY X

/-- 局所 K-flat 仮定を明示的に受け取る、実際の因子化関手の充満忠実性。 -/
def derivedQuotientLiftFullyFaithful (S : Set D) (h : localKFlat A D S) :
    (derivedQuotientLift A D S).FullyFaithful := by
  let : (derivedQuotientLift A D S).Full := {
    map_surjective := fun {X Y} f => (derivedQuotientLift_map_bijective A D S h X Y).2 f }
  let : (derivedQuotientLift A D S).Faithful := {
    map_injective := fun {X Y} f g he => (derivedQuotientLift_map_bijective A D S h X Y).1 he }
  exact Functor.FullyFaithful.ofFullyFaithful _

end SerrePositivity.DifferentialGraded.DGQuotient
