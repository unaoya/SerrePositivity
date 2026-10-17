module
public import SerrePositivity.DifferentialGraded.Verdier.PerfectNullComparison
public import Mathlib.CategoryTheory.Localization.LocalizerMorphism

/-! # 指定 Perf 商と既存 Karoubi-first 商・局所 perfect dg 商比較の同値 -/
@[expose] public section
noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Idempotents
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D] (S : Set D)

lemma karoubiPerfect_denominators :
    (karoubiNullEnvelope (triaImage A D S)).trW =
      (perfectNullObjects A D S).trW.inverseImage (finiteCellKaroubiToPerfect A D Set.univ) := by
  rw [karoubiNullEnvelope_eq_perfectNull A D S]
  ext X Y f
  exact (perfectNullObjects A D S).inverseImage_trW_iff _ f

def karoubiPerfectLocalizer :
    LocalizerMorphism (karoubiNullEnvelope (triaImage A D S)).trW
      (perfectNullObjects A D S).trW :=
  LocalizerMorphism.ofEq (karoubiPerfect_denominators A D S)

instance karoubiPerfectLocalizerIsLocalizedEquivalence :
    (karoubiPerfectLocalizer A D S).IsLocalizedEquivalence := by
  let Φ := karoubiPerfectLocalizer A D S
  have : Φ.functor.IsEquivalence := finiteCellKaroubiToPerfectIsEquivalence A D Set.univ
  apply LocalizerMorphism.IsLocalizedEquivalence.of_equivalence Φ
  change (perfectNullObjects A D S).trW ≤
    (karoubiNullEnvelope (triaImage A D S)).trW.map (finiteCellKaroubiToPerfect A D Set.univ)
  rw [karoubiPerfect_denominators, MorphismProperty.map_inverseImage_eq_of_isEquivalence]

def karoubiFirstPerfectQuotientFunctor :
    KaroubiFirstQuotient (triaImage A D S) ⥤ PerfectVerdierQuotient A D S :=
  (karoubiPerfectLocalizer A D S).localizedFunctor
    (karoubiNullEnvelope (triaImage A D S)).trW.Q (perfectVerdierQuotient A D S)

instance karoubiFirstPerfectQuotientLifting :
    Localization.Lifting (karoubiNullEnvelope (triaImage A D S)).trW.Q
      (karoubiNullEnvelope (triaImage A D S)).trW
      (finiteCellKaroubiToPerfect A D Set.univ ⋙ perfectVerdierQuotient A D S)
      (karoubiFirstPerfectQuotientFunctor A D S) := by
  change Localization.Lifting _ _
    ((karoubiPerfectLocalizer A D S).functor ⋙ perfectVerdierQuotient A D S)
    ((karoubiPerfectLocalizer A D S).localizedFunctor _ _)
  infer_instance

instance karoubiFirstPerfectQuotientFunctorIsEquivalence :
    (karoubiFirstPerfectQuotientFunctor A D S).IsEquivalence := by
  dsimp [karoubiFirstPerfectQuotientFunctor]
  infer_instance

def karoubiFirstPerfectQuotientEquivalence :
    KaroubiFirstQuotient (triaImage A D S) ≌ PerfectVerdierQuotient A D S :=
  (karoubiFirstPerfectQuotientFunctor A D S).asEquivalence

/-- 既存 Karoubi–Perf 同値を先に局所化した、指定商関手との正方形。 -/
def karoubiFirstPerfectQuotientSquare :
    (karoubiNullEnvelope (triaImage A D S)).trW.Q ⋙
        karoubiFirstPerfectQuotientFunctor A D S ≅
      finiteCellKaroubiToPerfect A D Set.univ ⋙ perfectVerdierQuotient A D S :=
  Localization.Lifting.iso _ (karoubiNullEnvelope (triaImage A D S)).trW _ _

instance karoubiFirstPerfectQuotientFunctorCommShift :
    (karoubiFirstPerfectQuotientFunctor A D S).CommShift ℤ :=
  Functor.commShiftOfLocalization (karoubiNullEnvelope (triaImage A D S)).trW.Q
    (karoubiNullEnvelope (triaImage A D S)).trW ℤ
    (finiteCellKaroubiToPerfect A D Set.univ ⋙ perfectVerdierQuotient A D S)
    (karoubiFirstPerfectQuotientFunctor A D S)

instance karoubiFirstPerfectQuotientSquareCommShift :
    NatTrans.CommShift (karoubiFirstPerfectQuotientSquare A D S).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization (karoubiNullEnvelope (triaImage A D S)).trW.Q
    (karoubiNullEnvelope (triaImage A D S)).trW ℤ
    (finiteCellKaroubiToPerfect A D Set.univ ⋙ perfectVerdierQuotient A D S)
    (karoubiFirstPerfectQuotientFunctor A D S)

instance karoubiFirstPerfectQuotientFunctorIsTriangulated :
    (karoubiFirstPerfectQuotientFunctor A D S).IsTriangulated := by
  have := Localization.essSurj_mapArrow (karoubiNullEnvelope (triaImage A D S)).trW.Q
    (karoubiNullEnvelope (triaImage A D S)).trW
  exact Functor.isTriangulated_of_precomp_iso (karoubiFirstPerfectQuotientSquare A D S)

instance karoubiFirstPerfectQuotientEquivalenceFunctorCommShift :
    (karoubiFirstPerfectQuotientEquivalence A D S).functor.CommShift ℤ :=
  karoubiFirstPerfectQuotientFunctorCommShift A D S
instance karoubiFirstPerfectQuotientEquivalenceInverseCommShift :
    (karoubiFirstPerfectQuotientEquivalence A D S).inverse.CommShift ℤ :=
  (karoubiFirstPerfectQuotientEquivalence A D S).commShiftInverse ℤ
instance karoubiFirstPerfectQuotientEquivalenceCommShift :
    (karoubiFirstPerfectQuotientEquivalence A D S).CommShift ℤ :=
  (karoubiFirstPerfectQuotientEquivalence A D S).commShift_of_functor ℤ
instance karoubiFirstPerfectQuotientEquivalenceIsTriangulated :
    (karoubiFirstPerfectQuotientEquivalence A D S).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _ (karoubiFirstPerfectQuotientFunctorIsTriangulated A D S)

instance karoubiPerfectCompletedFunctorCommShift :
    (karoubiEquivalenceTransport
      (karoubiFirstPerfectQuotientEquivalence A D S)).functor.CommShift ℤ := by
  change ((functorExtension₂ _ _).obj
    (karoubiFirstPerfectQuotientEquivalence A D S).functor).CommShift ℤ
  infer_instance
instance karoubiPerfectCompletedInverseCommShift :
    (karoubiEquivalenceTransport
      (karoubiFirstPerfectQuotientEquivalence A D S)).inverse.CommShift ℤ :=
  (karoubiEquivalenceTransport (karoubiFirstPerfectQuotientEquivalence A D S)).commShiftInverse ℤ
instance karoubiPerfectCompletedCommShift :
    (karoubiEquivalenceTransport (karoubiFirstPerfectQuotientEquivalence A D S)).CommShift ℤ :=
  (karoubiEquivalenceTransport
    (karoubiFirstPerfectQuotientEquivalence A D S)).commShift_of_functor ℤ
instance karoubiPerfectCompletedIsTriangulated :
    (karoubiEquivalenceTransport (karoubiFirstPerfectQuotientEquivalence A D S)).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _ (by
    change ((functorExtension₂ _ _).obj
      (karoubiFirstPerfectQuotientEquivalence A D S).functor).IsTriangulated
    infer_instance)

/-- 既存の完備化順序交換同値に接続した、指定 Perf 商の完備化。 -/
def perfectCompletedToTriaQuotientEquivalence :
    Karoubi (PerfectVerdierQuotient A D S) ≌ CompletedTriaQuotient A D S :=
  (karoubiEquivalenceTransport (karoubiFirstPerfectQuotientEquivalence A D S)).symm.trans
    (triaKaroubiOrderEquivalence A D S)

instance perfectCompletedToTriaQuotientFunctorCommShift :
    (perfectCompletedToTriaQuotientEquivalence A D S).functor.CommShift ℤ := by
  dsimp [perfectCompletedToTriaQuotientEquivalence]
  infer_instance
instance perfectCompletedToTriaQuotientInverseCommShift :
    (perfectCompletedToTriaQuotientEquivalence A D S).inverse.CommShift ℤ := by
  dsimp [perfectCompletedToTriaQuotientEquivalence]
  infer_instance
instance perfectCompletedToTriaQuotientCommShift :
    (perfectCompletedToTriaQuotientEquivalence A D S).CommShift ℤ := by
  dsimp [perfectCompletedToTriaQuotientEquivalence]
  infer_instance
instance perfectCompletedToTriaQuotientIsTriangulated :
    (perfectCompletedToTriaQuotientEquivalence A D S).IsTriangulated := by
  dsimp [perfectCompletedToTriaQuotientEquivalence]
  infer_instance

namespace DGQuotient
/-- 同じ指定商に値を持つ局所 perfect dg 商比較を、指定 Perf 商の完備化へ接続する。 -/
def localPerfectToPerfectVerdierEquivalence (h : localKFlat A D S) :
    PerfectDGHomotopyCategoryOver A (QuotientObject D S) Set.univ ≌
      Karoubi (PerfectVerdierQuotient A D S) :=
  (localPerfectQuotientEquivalence A D S h).trans
    (perfectCompletedToTriaQuotientEquivalence A D S).symm

instance localPerfectToPerfectVerdierFunctorCommShift (h : localKFlat A D S) :
    (localPerfectToPerfectVerdierEquivalence A D S h).functor.CommShift ℤ := by
  dsimp [localPerfectToPerfectVerdierEquivalence]
  infer_instance
instance localPerfectToPerfectVerdierInverseCommShift (h : localKFlat A D S) :
    (localPerfectToPerfectVerdierEquivalence A D S h).inverse.CommShift ℤ := by
  dsimp [localPerfectToPerfectVerdierEquivalence]
  infer_instance
instance localPerfectToPerfectVerdierCommShift (h : localKFlat A D S) :
    (localPerfectToPerfectVerdierEquivalence A D S h).CommShift ℤ := by
  dsimp [localPerfectToPerfectVerdierEquivalence]
  infer_instance
instance localPerfectToPerfectVerdierIsTriangulated (h : localKFlat A D S) :
    (localPerfectToPerfectVerdierEquivalence A D S h).IsTriangulated := by
  dsimp [localPerfectToPerfectVerdierEquivalence]
  infer_instance
end DGQuotient
end SerrePositivity.DifferentialGraded
