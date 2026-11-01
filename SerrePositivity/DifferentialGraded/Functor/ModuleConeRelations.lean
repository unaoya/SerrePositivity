module
public import SerrePositivity.DifferentialGraded.Functor.ModuleCone
public import SerrePositivity.DifferentialGraded.Module.ConeElementRelations
public import SerrePositivity.DifferentialGraded.Bimodule.Tensor

/-! # 複体値dg関手で送ったconeの行列恒等式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGFunctor
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (F : DGFunctor A (RightModule A D) (Complex A)) {M N : ModuleCategory A D}

def moduleConeImageFst (f : M ⟶ N) :
    Cochain ((F.toComplexFunctor A).obj (moduleCone A D f)) ((F.toComplexFunctor A).obj M) 1 :=
  (F.map (ForgetEnrichment.to (Complex A) (moduleCone A D f))
    (ForgetEnrichment.to (Complex A) M)).f 1 (moduleConeFstElement A D f)

def moduleConeImageSnd (f : M ⟶ N) :
    Cochain ((F.toComplexFunctor A).obj (moduleCone A D f)) ((F.toComplexFunctor A).obj N) 0 :=
  (F.map (ForgetEnrichment.to (Complex A) (moduleCone A D f))
    (ForgetEnrichment.to (Complex A) N)).f 0 (moduleConeSndElement A D f)

lemma moduleConeImage_inl_fst (f : M ⟶ N) :
    (moduleConeImageInl A D F f).comp (moduleConeImageFst A D F f) (neg_add_cancel 1) =
      Cochain.ofHom (𝟙 ((F.toComplexFunctor A).obj M)) := by
  have h := congrArg (fun z => (F.map (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) M)).f 0 z) (moduleCone_inl_fst A D f)
  rw [map_compose_cochain, map_unitElement, Bimodule.complex_unitElement] at h
  exact h

lemma moduleConeImage_inl_snd (f : M ⟶ N) :
    (moduleConeImageInl A D F f).comp (moduleConeImageSnd A D F f) (add_zero (-1)) = 0 := by
  have h := congrArg (fun z => (F.map (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) N)).f (-1) z) (moduleCone_inl_snd A D f)
  rw [map_compose_cochain, map_zero] at h
  exact h

lemma moduleConeImage_inr_fst (f : M ⟶ N) :
    (Cochain.ofHom ((F.toComplexFunctor A).map (moduleConeInr A D f))).comp
      (moduleConeImageFst A D F f) (zero_add 1) = 0 := by
  have h := congrArg (fun z => (F.map (ForgetEnrichment.to (Complex A) N)
    (ForgetEnrichment.to (Complex A) M)).f 1 z) (moduleCone_inr_fst A D f)
  rw [map_compose_cochain, moduleConeInrElement, map_closedElement, map_zero] at h
  exact h

lemma moduleConeImage_inr_snd (f : M ⟶ N) :
    (Cochain.ofHom ((F.toComplexFunctor A).map (moduleConeInr A D f))).comp
      (moduleConeImageSnd A D F f) (zero_add 0) =
      Cochain.ofHom (𝟙 ((F.toComplexFunctor A).obj N)) := by
  have h := congrArg (fun z => (F.map (ForgetEnrichment.to (Complex A) N)
    (ForgetEnrichment.to (Complex A) N)).f 0 z) (moduleCone_inr_snd A D f)
  rw [map_compose_cochain, moduleConeInrElement, map_closedElement,
    map_unitElement, Bimodule.complex_unitElement] at h
  exact h

lemma moduleConeImage_decomposition (f : M ⟶ N) :
    (moduleConeImageFst A D F f).comp (moduleConeImageInl A D F f) (add_neg_cancel 1) +
      (moduleConeImageSnd A D F f).comp
        (Cochain.ofHom ((F.toComplexFunctor A).map (moduleConeInr A D f))) (add_zero 0) =
      Cochain.ofHom (𝟙 ((F.toComplexFunctor A).obj (moduleCone A D f))) := by
  have h := congrArg (fun z =>
    (F.map (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).f 0 z)
    (moduleCone_decomposition A D f)
  rw [map_add, map_compose_cochain, map_compose_cochain, moduleConeInrElement,
    map_closedElement, map_unitElement, Bimodule.complex_unitElement] at h
  exact h

end SerrePositivity.DifferentialGraded.DGFunctor
