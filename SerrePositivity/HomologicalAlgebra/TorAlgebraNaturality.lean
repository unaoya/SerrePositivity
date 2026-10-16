module

public import SerrePositivity.HomologicalAlgebra.TorAlgebraScalarComparison

/-! # Algebra-valued Tor comparisons preserve the original test-module maps -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory
variable {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]

/-- Naturality for arbitrary specified resolution maps, with their original augmentation square. -/
@[reassoc] lemma algebraResolutionTorComparison_naturality
    {M N : ModuleCat.{u} R} {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsResolutionOf K M) (hL : IsResolutionOf L N) (f : K ⟶ L) (g : M ⟶ N)
    (h : HomologicalComplex.homologyMap f 0 ≫ hL.homologyZeroIso.hom =
      hK.homologyZeroIso.hom ≫ g) (i : ℕ) :
    ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R C)).map g ≫
        (algebraResolutionTorComparison (C := C) hL i).hom =
      (algebraResolutionTorComparison (C := C) hK i).hom ≫
        (ModuleCat.restrictScalars (algebraMap R C)).map
          (HomologicalComplex.homologyMap ((ModuleCat.extendScalars
            (algebraMap R C)).mapHomologicalComplex (.up ℤ) |>.map f) (-(i : ℤ))) := by
  let U := ModuleCat.restrictScalars (algebraMap R C)
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) (-(i : ℤ))
  let F := (tensoringLeft (ModuleCat R)).obj (ModuleCat.of R C)
  let b := ((ModuleCat.extendScalars (algebraMap R C)).mapHomologicalComplex (.up ℤ)).map f
  let eK := algebraBaseChangeTensorIso (C := C) K
  let eL := algebraBaseChangeTensorIso (C := C) L
  let qK := (restrictCochainHomologyIso (R := R) (C := C) (-(i : ℤ))).app
    (baseChange (algebraMap R C) K)
  let qL := (restrictCochainHomologyIso (R := R) (C := C) (-(i : ℤ))).app
    (baseChange (algebraMap R C) L)
  have ht : ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R C)).map g ≫
      (torModuleIsoCochain C hL i).hom =
      (torModuleIsoCochain C hK i).hom ≫ H.map ((F.mapHomologicalComplex (.up ℤ)).map f) :=
    leftDerivedIsoCochain_hom_naturality F hK hL f g h i
  have he : (U.mapHomologicalComplex (.up ℤ)).map b ≫ eL.hom =
      eK.hom ≫ (F.mapHomologicalComplex (.up ℤ)).map f :=
    (Functor.mapHomologicalComplexCompIso
      (extendRestrictScalarsTensorIso (R := R) (T := C)) (.up ℤ)).hom.naturality f
  have hei : (F.mapHomologicalComplex (.up ℤ)).map f ≫ eL.inv =
      eK.inv ≫ (U.mapHomologicalComplex (.up ℤ)).map b := by
    apply (cancel_epi eK.hom).mp
    rw [← Category.assoc, ← he, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.hom_inv_id_assoc]
  have hh := congrArg H.map hei
  simp only [Functor.map_comp] at hh
  have hq := (restrictCochainHomologyIso (R := R) (C := C) (-(i : ℤ))).hom.naturality b
  change H.map ((U.mapHomologicalComplex (.up ℤ)).map b) ≫ qL.hom =
    qK.hom ≫ U.map (HomologicalComplex.homologyMap b (-(i : ℤ))) at hq
  change _ ≫ ((torModuleIsoCochain C hL i).hom ≫ H.map eL.inv ≫ qL.hom) =
    ((torModuleIsoCochain C hK i).hom ≫ H.map eK.inv ≫ qK.hom) ≫ _
  rw [reassoc_of% ht, reassoc_of% hh, hq]
  simp only [Category.assoc]
  rfl

/-- The comparison with the actual algebra-valued Tor is natural for every test map. -/
@[reassoc] lemma torAlgebraComparison_naturality
    {M N : ModuleCat.{u} R} (f : M ⟶ N) (i : ℕ) :
    ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R C)).map f ≫
        (torAlgebraComparison (C := C) N i).hom =
      (torAlgebraComparison (C := C) M i).hom ≫
        (ModuleCat.restrictScalars (algebraMap R C)).map
          (((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).map f) := by
  let U := ModuleCat.restrictScalars (algebraMap R C)
  let P := projectiveResolution M
  let Q := projectiveResolution N
  let k := extLift P f Q
  let hP := isResolutionOf_extRes P
  let hQ := isResolutionOf_extRes Q
  let eP := torIsoCochain (algebraMap R C) hP i
  let eQ := torIsoCochain (algebraMap R C) hQ i
  let b := ((ModuleCat.extendScalars (algebraMap R C)).mapHomologicalComplex (.up ℤ)).map k
  have ht := algebraResolutionTorComparison_naturality (C := C) hP hQ k f
    (extLift_homologyZero P f Q) i
  have hb := leftDerivedIsoCochain_hom_naturality
    (ModuleCat.extendScalars (algebraMap R C)) hP hQ k f (extLift_homologyZero P f Q) i
  change ((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).map f ≫ eQ.hom =
    eP.hom ≫ HomologicalComplex.homologyMap b (-(i : ℤ)) at hb
  have hbi : HomologicalComplex.homologyMap b (-(i : ℤ)) ≫ eQ.inv =
      eP.inv ≫ ((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).map f := by
    apply (cancel_epi eP.hom).mp
    rw [← Category.assoc, ← hb, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.hom_inv_id_assoc]
  have hu := congrArg U.map hbi
  simp only [Functor.map_comp] at hu
  simp only [torAlgebraComparison, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, ht, Category.assoc, hu]
  simp only [Category.assoc]
  rfl

/-- Naturality packaged for the original standard and algebra-valued Tor functors. -/
def torAlgebraComparisonNatIso (i : ℕ) :
    (Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R C) ≅
      (ModuleCat.extendScalars (algebraMap R C)).leftDerived i ⋙
        ModuleCat.restrictScalars (algebraMap R C) :=
  NatIso.ofComponents (fun M => torAlgebraComparison M i)
    (fun f => torAlgebraComparison_naturality f i)

end SerrePositivity
