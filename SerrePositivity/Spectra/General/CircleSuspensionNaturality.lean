module

public import SerrePositivity.Spectra.General.CircleHomotopySuspension
public import SerrePositivity.HomotopicalAlgebra.Pointed.SuspensionNaturality
public import Mathlib.AlgebraicTopology.ModelCategory.CofibrantObjectHomotopy

/-! # Naturality of circle tensor versus ordinary homotopy suspension

Both endpoints of the actual interval cylinder and the actual quotient
map are natural in the spectrum. The generic cone comparison therefore
gives a natural isomorphism on the full category of cofibrant spectra.
-/

@[expose] public section
universe w u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Quillen SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.GeneralSymmetricSpectrum
variable {K : PointedSimplicialSet.{u}}

def simplicialVertexNatIso :
    pointwiseTensorFunctor (K := K)
      (PointedObject.adjoin (SSet.stdSimplex.{u}.obj (SimplexCategory.mk 0))) ≅
        𝟭 (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K) :=
  (pointwiseTensorBifunctor (K := K)).mapIso
    (PointedObject.adjoinFunctor.mapIso QuillenStandardFrame.zeroUnitIso.{u}) ≪≫
      pointwiseTensorUnitNatIso

@[simp] lemma simplicialVertexNatIso_app
    (E : GeneralSymmetricSpectrum PointedSimplicialSet.{u} K) :
    simplicialVertexNatIso.app E = simplicialVertexIso E := rfl

abbrev simplicialIntervalMap {E F : GeneralSymmetricSpectrum PointedSimplicialSet.{u} K}
    (f : E ⟶ F) :=
  (pointwiseTensorFunctor (K := K) (PointedObject.adjoin
    (SSet.stdSimplex.{u}.obj (SimplexCategory.mk 1)))).map f

lemma simplicialEndpoint_naturality {E F : GeneralSymmetricSpectrum PointedSimplicialSet.{u} K}
    (f : E ⟶ F) (i : Fin 2) :
    ((simplicialVertexIso E).inv ≫
      (simplicialParameterFunctor E).map (SSet.stdSimplex.map (SimplexCategory.δ i))) ≫
        simplicialIntervalMap f = f ≫ (simplicialVertexIso F).inv ≫
          (simplicialParameterFunctor F).map (SSet.stdSimplex.map (SimplexCategory.δ i)) := by
  have hv : f ≫ (simplicialVertexIso F).inv = (simplicialVertexIso E).inv ≫
      (pointwiseTensorFunctor (K := K) (PointedObject.adjoin
        (SSet.stdSimplex.{u}.obj (SimplexCategory.mk 0)))).map f := by
    simpa only [← Iso.app_inv, simplicialVertexNatIso_app, Functor.id_map] using
      (simplicialVertexNatIso (K := K)).inv.naturality f
  have hn : (simplicialParameterFunctor E).map
      (SSet.stdSimplex.map (SimplexCategory.δ i)) ≫ simplicialIntervalMap f =
      (pointwiseTensorFunctor (K := K) (PointedObject.adjoin
        (SSet.stdSimplex.{u}.obj (SimplexCategory.mk 0)))).map f ≫
      (simplicialParameterFunctor F).map (SSet.stdSimplex.map (SimplexCategory.δ i)) :=
    (((pointwiseTensorBifunctor (K := K)).map (PointedObject.adjoinFunctor.map
      (SSet.stdSimplex.map (SimplexCategory.δ i)))).naturality f).symm
  rw [Category.assoc, hn, ← Category.assoc, ← hv, Category.assoc]

lemma circleTensorQuotient_naturality
    {E F : GeneralSymmetricSpectrum PointedSimplicialSet.{u} K} (f : E ⟶ F) :
    circleTensorQuotient E ≫ (pointwiseTensorFunctor (K := K) PointedSimplicialSet.circle).map f =
      simplicialIntervalMap f ≫ circleTensorQuotient F :=
  (((pointwiseTensorBifunctor (K := K)).map
    (PointedObject.cofiberProjection (SSet.boundary.{u} 1).ι)).naturality f).symm

variable [ModelCategory SSet.{u}]
  [spectrumModel : ModelCategory (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K)]
  [IsQuillenBifunctor (pointwiseTensorBifunctor (K := K))]
  (hcof : cofibrations SSet.{u} = MorphismProperty.monomorphisms _)
  (hw : weakEquivalences SSet.{u} = SimplicialHomotopy.weakEquivalences)
  {E F : GeneralSymmetricSpectrum PointedSimplicialSet.{u} K} [IsCofibrant E] [IsCofibrant F]

lemma simplicialCylinder_i₀_naturality (f : E ⟶ F) :
    (simplicialCylinder hcof hw E).i₀ ≫ simplicialIntervalMap f =
      f ≫ (simplicialCylinder hcof hw F).i₀ := by
  exact simplicialEndpoint_naturality f (1 : Fin 2)

lemma simplicialCylinder_i₁_naturality (f : E ⟶ F) :
    (simplicialCylinder hcof hw E).i₁ ≫ simplicialIntervalMap f =
      f ≫ (simplicialCylinder hcof hw F).i₁ := by
  exact simplicialEndpoint_naturality f (0 : Fin 2)

variable [IsLocallyPresentable.{w} (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K)]
  (I J : MorphismProperty (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K))
  [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [MorphismProperty.IsStableUnderCobaseChangeAgainst
    (weakEquivalences (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K))
    (cofibrations (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K))]
  {H : Type uH} [Category.{vH} H]
  (Q : GeneralSymmetricSpectrum PointedSimplicialSet.{u} K ⥤ H)
  [Q.IsLocalization (weakEquivalences (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K))]

lemma circleHomotopySuspensionIso_naturality (f : E ⟶ F) :
    Q.map ((HomotopySuspension.functor I J).map f) ≫
      (circleHomotopySuspensionIso hcof hw F I J Q).hom =
        (circleHomotopySuspensionIso hcof hw E I J Q).hom ≫
          Q.map ((pointwiseTensorFunctor (K := K) PointedSimplicialSet.circle).map f) := by
  have := simplicialCylinder_isGood hcof hw E
  have := simplicialCylinder_isGood hcof hw F
  exact HomotopySuspension.cylinderQuotientIso_naturality I J
    (P := simplicialCylinder hcof hw E) (R := simplicialCylinder hcof hw F)
    (f := f) (k := simplicialIntervalMap f)
    (h₀ := simplicialCylinder_i₀_naturality hcof hw f)
    (h₁ := simplicialCylinder_i₁_naturality hcof hw f) (Q := Q)
    (q := circleTensorQuotient E) (r := circleTensorQuotient F)
    (sq := circleTensor_zeroCylinder_isPushout hcof hw E)
    (sr := circleTensor_zeroCylinder_isPushout hcof hw F)
    (z := (pointwiseTensorFunctor (K := K) PointedSimplicialSet.circle).map f)
    (hz := circleTensorQuotient_naturality f)

def circleSuspensionCofibrantNatIso :
    CofibrantObject.ι ⋙ (HomotopySuspension.functor I J ⋙ Q) ≅
      CofibrantObject.ι ⋙ (pointwiseTensorFunctor (K := K) PointedSimplicialSet.circle ⋙ Q) :=
  NatIso.ofComponents
    (fun E ↦ circleHomotopySuspensionIso hcof hw E.obj I J Q)
    (fun f ↦ circleHomotopySuspensionIso_naturality hcof hw I J Q f.hom)

end SerrePositivity.GeneralSymmetricSpectrum
