module
public import SerrePositivity.DifferentialGraded.Functor.ModuleShift
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.Data.ZMod.Basic

/-! # 主Hom内と複体値dg関手の像でのcone行列恒等式 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGFunctor
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example {M N : ModuleCategory A D} (f : M ⟶ N) :
    compose A (moduleConeFstElement A D f) (moduleConeInlElement A D f) (neg_add_cancel 1) =
      (unitElement A (ForgetEnrichment.to (Complex A) M)).val :=
  moduleCone_inl_fst A D f

example (F : DGFunctor A (RightModule A D) (Complex A)) {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleConeImageFst A D F f).comp (moduleConeImageInl A D F f) (add_neg_cancel 1) +
      (moduleConeImageSnd A D F f).comp
        (Cochain.ofHom ((F.toComplexFunctor A).map (moduleConeInr A D f))) (add_zero 0) =
      Cochain.ofHom (𝟙 ((F.toComplexFunctor A).obj (moduleCone A D f))) :=
  moduleConeImage_decomposition A D F f

example {M N : ModuleCategory (ZMod 2) PUnit.{1}} (f : M ⟶ N) :
    compose (ZMod 2) (moduleConeFstElement (ZMod 2) PUnit.{1} f)
      (moduleConeInlElement (ZMod 2) PUnit.{1} f) (neg_add_cancel 1) =
      (unitElement (ZMod 2) (ForgetEnrichment.to (Complex (ZMod 2)) M)).val :=
  moduleCone_inl_fst (ZMod 2) PUnit.{1} f

#print axioms moduleConeInrElement
#print axioms moduleConeInrElement_π
#print axioms moduleCone_inl_fst
#print axioms moduleCone_inl_snd
#print axioms moduleCone_inr_fst
#print axioms moduleCone_inr_snd
#print axioms moduleCone_decomposition
#print axioms moduleConeImageFst
#print axioms moduleConeImageSnd
#print axioms moduleConeImage_inl_fst
#print axioms moduleConeImage_inl_snd
#print axioms moduleConeImage_inr_fst
#print axioms moduleConeImage_inr_snd
#print axioms moduleConeImage_decomposition
