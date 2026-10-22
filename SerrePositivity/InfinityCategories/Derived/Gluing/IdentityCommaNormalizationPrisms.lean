module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ClosedCompositionPrisms
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaNormalizeHom

/-! 恒等 comma の実標準閉射での正規化前後合成を、同じ実 slice 三角形の全族として保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]
  (X Y : DGFunctorCommaObject R E E (DGFunctor.id E))
  {K : SSet.{max u v}} (f : K ⟶ DGNerve.pinchedHom R
    (DGFunctorCommaObject R E E (DGFunctor.id E)) X Y)
local notation "Q" => DGFunctorCommaObject R E E (DGFunctor.id E)
local notation "NX" => dgGluingIdentityCommaObject R E X.replacement
local notation "NY" => dgGluingIdentityCommaObject R E Y.source

def dgGluingIdentityCommaPreNormalizePrism :=
  dgGluingClosedPrecompositionPrism R Q (dgGluingIdentityCommaNormalizationClosedIn R E X) f

lemma dgGluingIdentityCommaPreNormalizePrism_zero :
    prismEndpoint 0 K ≫ dgGluingIdentityCommaPreNormalizePrism R E X Y f =
      f ≫ pinchedHomChainMap (D := Q) (E := Q)
        (dgGluingIdentityCommaPreNormalizeHom R E X Y) ≫ dgPinchedHomSlice R Q NX Y := by
  rw [dgGluingIdentityCommaPreNormalizePrism, dgGluingClosedPrecompositionPrism_zero,
    dgGluingIdentityCommaPreNormalizeHom_closed]

lemma dgGluingIdentityCommaPreNormalizePrism_one :
    prismEndpoint 1 K ≫ dgGluingIdentityCommaPreNormalizePrism R E X Y f =
      f ≫ dgPinchedHomSlice R Q X Y :=
  dgGluingClosedPrecompositionPrism_one R Q _ f

lemma dgGluingIdentityCommaPreNormalizePrism_projection :
    dgGluingIdentityCommaPreNormalizePrism R E X Y f ≫ sliceOverProjection _ =
      intervalMappingUncurry ((SSet.const (X := K)
        (pinchedClosedVertex R Q (dgGluingIdentityCommaNormalizationClosedIn R E X))) ≫
          pinchedHomToIntervalMappingSpace (X := dgNerve R Q)
            (Simplex.vertex NX) (Simplex.vertex X)) :=
  dgGluingClosedPrecompositionPrism_projection R Q _ f

def dgGluingIdentityCommaPostNormalizePrism :=
  dgGluingClosedPostcompositionPrism R Q
    (dgGluingIdentityCommaNormalizationClosedOut R E Y)
    (f ≫ pinchedHomChainMap (D := Q) (E := Q)
      (dgGluingIdentityCommaPreNormalizeHom R E X Y))

lemma dgGluingIdentityCommaPostNormalizePrism_zero :
    prismEndpoint 0 K ≫ dgGluingIdentityCommaPostNormalizePrism R E X Y f =
      f ≫ pinchedHomChainMap (D := Q) (E := Q)
        (dgGluingIdentityCommaNormalizeHom R E X Y) ≫ dgPinchedHomSlice R Q NX NY := by
  rw [dgGluingIdentityCommaPostNormalizePrism, dgGluingClosedPostcompositionPrism_zero,
    ← dgGluingIdentityCommaPostNormalizeHom_closed R E NX Y]
  have hc := pinchedHomChainMap_comp (D := Q) (E := Q) (T := Q)
    (x := X) (y := Y) (x' := NX) (y' := Y) (x'' := NX) (y'' := NY)
    (dgGluingIdentityCommaPreNormalizeHom R E X Y)
    (dgGluingIdentityCommaPostNormalizeHom R E NX Y)
  rw [dgGluingIdentityCommaNormalizeHom, hc]
  simp only [Category.assoc]

lemma dgGluingIdentityCommaPostNormalizePrism_one :
    prismEndpoint 1 K ≫ dgGluingIdentityCommaPostNormalizePrism R E X Y f =
      (SSet.const (X := K)
        (pinchedClosedVertex R Q (dgGluingIdentityCommaNormalizationClosedOut R E Y))) ≫
          dgPinchedHomSlice R Q Y NY :=
  dgGluingClosedPostcompositionPrism_one R Q _ _

lemma dgGluingIdentityCommaPostNormalizePrism_projection :
    dgGluingIdentityCommaPostNormalizePrism R E X Y f ≫ sliceOverProjection _ =
      intervalMappingUncurry ((f ≫ pinchedHomChainMap (D := Q) (E := Q)
        (dgGluingIdentityCommaPreNormalizeHom R E X Y)) ≫
          pinchedHomToIntervalMappingSpace (X := dgNerve R Q)
            (Simplex.vertex NX) (Simplex.vertex Y)) :=
  dgGluingClosedPostcompositionPrism_projection R Q _ _

end SerrePositivity.InfinityCategories
