module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSourceImageSourceLayer
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSourceImageTargetLayer
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageFactorisationConnectivity

/-!
概要：元の上段射の実因子分解の二射は、層同型の下で元の像射影と像包含になる。
方針：源射の厳密な比較式と、標的射の実乗法的経路をホモロジーへ送る。
規約：上段・中間代数の同型を明示。使われ方：LT の連結な像分解の層での全射・単射。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (f : B ⟶ C) (n : ℤ) (hn : 0 ≤ n)

lemma postnikovImageFactorisationSource_layer :
    homologyMap (postnikovImageFactorisationSource R f n hn).hom (-(n + 1)) ≫
      (postnikovImageFactorisationLayerHomologyIso R f n hn).hom =
        (postnikovUpperClassLayerHomologyIso R B n hn).hom ≫
          factorThruImage (homologyMap f.hom (-(n + 1))) := by
  have he : (postnikovImageFactorisationSource R f n hn).hom ≫
      (postnikovImageFactorisationComparison R f n hn).hom =
        (postnikovSourceImageFactor R f n hn).hom :=
    congrArg Mon.Hom.hom (postnikovImageFactorisationSource_comparison R f n hn)
  change homologyMap (postnikovImageFactorisationSource R f n hn).hom (-(n + 1)) ≫
    homologyMap (postnikovImageFactorisationComparison R f n hn).hom (-(n + 1)) ≫
      (postnikovSourceImageLayerHomologyIso R f n hn).hom = _
  rw [← Category.assoc, ← homologyMap_comp, he, postnikovSourceImageFactor_layer]

lemma postnikovImageFactorisationTarget_layer :
    homologyMap (postnikovImageFactorisationTarget R f n hn).hom (-(n + 1)) ≫
      (postnikovUpperClassLayerHomologyIso R C n hn).hom =
        (postnikovImageFactorisationLayerHomologyIso R f n hn).hom ≫
          image.ι (homologyMap f.hom (-(n + 1))) := by
  have he : homologyMap ((postnikovImageFactorisationComparison R f n hn).hom ≫
        (postnikovSourceImageToTarget R f n hn).hom) (-(n + 1)) =
      homologyMap ((postnikovImageFactorisationTarget R f n hn).hom ≫
        (postnikovHomotopyPullbackComparison R C n hn).hom) (-(n + 1)) :=
    (HomotopyPullbackModel.witness R (postnikovSourceImageToTarget R f n hn)
      (postnikovHomotopyPullbackComparison R C n hn)).chainHomotopy.homologyMap_eq _
  change homologyMap (postnikovImageFactorisationTarget R f n hn).hom (-(n + 1)) ≫
    (homologyMap (postnikovHomotopyPullbackComparison R C n hn).hom (-(n + 1)) ≫
      (postnikovClassModelLayerHomologyIso R C n hn).hom) =
        (homologyMap (postnikovImageFactorisationComparison R f n hn).hom (-(n + 1)) ≫
          (postnikovSourceImageLayerHomologyIso R f n hn).hom) ≫ _
  rw [← Category.assoc, ← homologyMap_comp, ← he, homologyMap_comp,
    Category.assoc, postnikovSourceImageToTarget_layer, Category.assoc]

lemma postnikovImageFactorisationSource_layer_epi :
    Epi (homologyMap (postnikovImageFactorisationSource R f n hn).hom (-(n + 1))) := by
  apply (epi_comp_iff_of_isIso _ (postnikovImageFactorisationLayerHomologyIso R f n hn).hom).1
  rw [postnikovImageFactorisationSource_layer]
  infer_instance

lemma postnikovImageFactorisationTarget_layer_mono :
    Mono (homologyMap (postnikovImageFactorisationTarget R f n hn).hom (-(n + 1))) :=
  mono_of_mono_fac (postnikovImageFactorisationTarget_layer R f n hn)

lemma postnikovUpperClassLayerHomologyIso_naturality :
    homologyMap (postnikovMap R f (n + 1)).hom (-(n + 1)) ≫
      (postnikovUpperClassLayerHomologyIso R C n hn).hom =
        (postnikovUpperClassLayerHomologyIso R B n hn).hom ≫
          homologyMap f.hom (-(n + 1)) := by
  have he : (postnikovImageFactorisationSource R f n hn).hom ≫
      (postnikovImageFactorisationTarget R f n hn).hom = (postnikovMap R f (n + 1)).hom :=
    congrArg Mon.Hom.hom (postnikovImageFactorisation_fac R f n hn)
  rw [← he, homologyMap_comp, Category.assoc, postnikovImageFactorisationTarget_layer,
    ← Category.assoc, postnikovImageFactorisationSource_layer, Category.assoc, image.fac]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
