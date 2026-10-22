module

public import SerrePositivity.KST.LocalizingInvariants.DGBimoduleImageKernel
public import SerrePositivity.KST.LocalizingInvariants.DGBimoduleCokernelSupport
public import SerrePositivity.KST.LocalizingInvariants.CochainEpiHomologyUpperBound

/-!
概要：源の上界と標的の下界が一致する次数では、実係数像のホモロジーも元の像を表す。
方針：短完全列の長完全列で元の包含と射影の単射・全射性を証明し、像の普遍性を使う。
規約：元の二射のホモロジーを保持。使われ方：Postnikov の係数像の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGBimoduleImage
variable {R : Type u} [CommRing R] {A : Mon (Complex R)} {M N : Bimod A A} (f : M ⟶ N)

lemma homology_inclusion_mono (k : ℤ) [N.X.IsStrictlyGE k] :
    Mono (homologyMap (inclusion f).hom k) := by
  have : (DGBimoduleCokernel.obj f).X.IsStrictlyGE k := DGBimoduleCokernel.lowerBound f k
  have hz := (DGBimoduleCokernel.obj f).X.isZero_of_isGE k (k - 1) (by omega)
  exact ((shortComplex_shortExact f).homology_exact₁ (k - 1) k
    (by change k - 1 + 1 = k; omega)).mono_g (hz.eq_of_src _ _)

lemma homology_projection_epi (k : ℤ) [M.X.IsStrictlyLE k] :
    Epi (homologyMap (projection f).hom k) := by
  have := projection_epi f
  exact cochainEpi_homologyMap_epi _ k

lemma homology_fac (k : ℤ) : homologyMap (projection f).hom k ≫ homologyMap (inclusion f).hom k =
    homologyMap f.hom k := by
  have hf : (projection f).hom ≫ (inclusion f).hom = f.hom :=
    congrArg Bimod.Hom.hom (projection_inclusion f)
  exact (homologyMap_comp (projection f).hom (inclusion f).hom k).symm.trans
    (congrArg (fun t : M.X ⟶ N.X => homologyMap t k) hf)

variable (k : ℤ) [M.X.IsStrictlyLE k] [N.X.IsStrictlyGE k]

def homologyFactorisation : StrongEpiMonoFactorisation (homologyMap f.hom k) where
  I := (obj f).X.homology k
  m := homologyMap (inclusion f).hom k
  e := homologyMap (projection f).hom k
  fac := homology_fac f k
  m_mono := homology_inclusion_mono f k
  e_strong_epi := by
    have := homology_projection_epi f k
    exact strongEpi_of_epi _

def homologyImageIso : (obj f).X.homology k ≅ image (homologyMap f.hom k) :=
  IsImage.isoExt (homologyFactorisation f k).toMonoIsImage (Image.isImage _)

lemma homologyImageIso_inclusion : (homologyImageIso f k).hom ≫ image.ι (homologyMap f.hom k) =
    homologyMap (inclusion f).hom k := by
  exact IsImage.isoExt_hom_m _ _

lemma homologyImageIso_projection : homologyMap (projection f).hom k ≫
    (homologyImageIso f k).hom = factorThruImage (homologyMap f.hom k) :=
  IsImage.e_isoExt_hom (homologyFactorisation f k).toMonoIsImage
    (Image.isImage (homologyMap f.hom k))

end SerrePositivity.KST.LocalizingInvariants.DGBimoduleImage
