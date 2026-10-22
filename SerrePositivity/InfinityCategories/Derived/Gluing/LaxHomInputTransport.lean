module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomPullbackComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedCompositeTransport

/-! F2 の入力側射影を、元の二 dg 射影の対の写像空間作用へ厳密に戻す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
local notation "F" => dgGluingUniverseDerivedNerveLaxComparison R C D M

lemma dgGluingUniverseDerivedNerveLaxComparison_inputs :
    (F) ≫ pullback.snd
        (F2.arrowEndpointPair
          ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
            (dgModuleDerivedInfinityCategory R C)))
        (dgGluingUniverseDerivedYoneda.{u, v, w} R C ⊗ₘ
          dgGluingUniverseDerivedCoefficient R C D M) =
      lift (dgGluingUniverseLeftNerve R C D M) (dgGluingUniverseRightNerve R C D M) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [lift_fst]
    simpa only [Category.assoc, F2.laxPullbackFst] using
      dgGluingUniverseDerivedNerveLaxComparison_fst R C D M
  · rw [lift_snd]
    simpa only [Category.assoc, F2.laxPullbackSnd] using
      dgGluingUniverseDerivedNerveLaxComparison_snd R C D M

def dgGluingLaxHomInputEndpointIso (X Y : DGGluingObject R C D M) :=
  dgGluingPinchedCompositeIso (F)
    (pullback.snd
      (F2.arrowEndpointPair
        ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
          (dgModuleDerivedInfinityCategory R C)))
      (dgGluingUniverseDerivedYoneda.{u, v, w} R C ⊗ₘ
        dgGluingUniverseDerivedCoefficient R C D M))
    (lift (dgGluingUniverseLeftNerve R C D M) (dgGluingUniverseRightNerve R C D M))
    (dgGluingUniverseDerivedNerveLaxComparison_inputs R C D M)
    (ULift.up (Simplex.vertex X)) (ULift.up (Simplex.vertex Y))

lemma dgGluingLaxHomPullbackComparison_inputs_transport (X Y : DGGluingObject R C D M) :
    dgGluingLaxHomPullbackComparison R C D M X Y ≫ pullback.snd _ _ ≫
      (dgGluingLaxHomInputEndpointIso R C D M X Y).hom =
    (dgGluingUniverseHomMappingIso R C D M X Y).inv ≫
      pinchedHomMap
        (lift (dgGluingUniverseLeftNerve R C D M) (dgGluingUniverseRightNerve R C D M))
        (ULift.up (Simplex.vertex X)) (ULift.up (Simplex.vertex Y)) := by
  rw [← Category.assoc, dgGluingLaxHomPullbackComparison_inputs,
    dgGluingLaxHomMappingComparison]
  simpa only [Category.assoc, dgGluingLaxHomInputEndpointIso] using
    congrArg (fun k => (dgGluingUniverseHomMappingIso R C D M X Y).inv ≫ k)
      (dgGluingPinchedComposite_naturality (F)
        (pullback.snd
          (F2.arrowEndpointPair
            ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
              (dgModuleDerivedInfinityCategory R C)))
          (dgGluingUniverseDerivedYoneda.{u, v, w} R C ⊗ₘ
            dgGluingUniverseDerivedCoefficient R C D M))
        (lift (dgGluingUniverseLeftNerve R C D M) (dgGluingUniverseRightNerve R C D M))
        (dgGluingUniverseDerivedNerveLaxComparison_inputs R C D M)
        (ULift.up (Simplex.vertex X)) (ULift.up (Simplex.vertex Y)))

end SerrePositivity.InfinityCategories
