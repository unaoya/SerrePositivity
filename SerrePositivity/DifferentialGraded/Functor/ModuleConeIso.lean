module
public import SerrePositivity.DifferentialGraded.Functor.ModuleConeRelations
public import SerrePositivity.DifferentialGraded.Complexes.ConeRepresentation

/-! # 複体値dg関手は主dg加群の標準coneを保つ -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGFunctor
open CategoryTheory CochainComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance moduleConeImageComparison_isIso (F : DGFunctor A (RightModule A D) (Complex A))
    {M N : ModuleCategory A D} (f : M ⟶ N) : IsIso (moduleConeImageComparison A D F f) :=
  complexConeDesc_isIso A ((F.toComplexFunctor A).map f)
    (moduleConeImageInl A D F f) ((F.toComplexFunctor A).map (moduleConeInr A D f))
    (moduleConeImageFst A D F f) (moduleConeImageSnd A D F f) (moduleConeImageInl_d A D F f)
    (moduleConeImage_inl_fst A D F f) (moduleConeImage_inl_snd A D F f)
    (moduleConeImage_inr_fst A D F f) (moduleConeImage_inr_snd A D F f)
    (moduleConeImage_decomposition A D F f)

/-- 非有界coneの実際の複体同型。 -/
def moduleConeImageIso (F : DGFunctor A (RightModule A D) (Complex A))
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    mappingCone ((F.toComplexFunctor A).map f) ≅ (F.toComplexFunctor A).obj (moduleCone A D f) :=
  asIso (moduleConeImageComparison A D F f)

lemma moduleConeImageIso_hom (F : DGFunctor A (RightModule A D) (Complex A))
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleConeImageIso A D F f).hom = moduleConeImageComparison A D F f := rfl

end SerrePositivity.DifferentialGraded.DGFunctor
