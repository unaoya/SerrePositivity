module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovExtensionBaseChange
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerHomology

/-!
概要：底変更した隣接拡大の実 kernel を、元の係数層と元の包含を保って比較する。
方針：元の kernel 同型の逆と標準層の準同型を合成し、両射影を厳密に回収する。
規約：kernel 自体の平方零性と混同しない。使われ方：高次底変更の実係数。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0] (n : ℤ)
  {P : Mon (Complex R)} (b : P ⟶ postnikov R B n)

def postnikovBaseChangedKernelIso :
    kernel (postnikovExtensionBaseChangeBase R B n b).hom ≅ postnikovKernel R B n :=
  ExtensionBaseChange.kernelIso R b (postnikovTransition R B (n + 1) n (by omega))

def postnikovBaseChangedLayerToKernel : postnikovLayer R B n ⟶
    kernel (postnikovExtensionBaseChangeBase R B n b).hom :=
  postnikovLayerToKernel R B n ≫ (postnikovBaseChangedKernelIso R B n b).inv

def postnikovBaseChangedLayerInclusion :
    postnikovLayer R B n ⟶ (postnikovExtensionBaseChange R B n b).X :=
  postnikovBaseChangedLayerToKernel R B n b ≫
    kernel.ι (postnikovExtensionBaseChangeBase R B n b).hom

lemma postnikovBaseChangedLayerToKernel_quasiIso :
    QuasiIso (postnikovBaseChangedLayerToKernel R B n b) :=
  quasiIso_comp _ _ (hφ := postnikovLayerToKernel_quasiIso R B n)
    (hφ' := quasiIso_of_isIso _)

lemma postnikovBaseChangedLayerInclusion_base : postnikovBaseChangedLayerInclusion R B n b ≫
    (postnikovExtensionBaseChangeBase R B n b).hom = 0 := by
  rw [postnikovBaseChangedLayerInclusion, Category.assoc, kernel.condition, comp_zero]

lemma postnikovBaseChangedLayerInclusion_upper : postnikovBaseChangedLayerInclusion R B n b ≫
    (postnikovExtensionBaseChangeUpper R B n b).hom = postnikovLayerInclusion R B n := by
  have he : (postnikovBaseChangedKernelIso R B n b).hom ≫ postnikovKernelInclusion R B n =
      kernel.ι (postnikovExtensionBaseChangeBase R B n b).hom ≫
        (postnikovExtensionBaseChangeUpper R B n b).hom :=
    ExtensionBaseChange.kernelMap_inclusion R b _
  change ((postnikovLayerToKernel R B n ≫ (postnikovBaseChangedKernelIso R B n b).inv) ≫
    kernel.ι (postnikovExtensionBaseChangeBase R B n b).hom) ≫ _ = _
  rw [Category.assoc, Category.assoc, ← he, Iso.inv_hom_id_assoc]
  exact postnikovLayerToKernel_inclusion R B n


def postnikovBaseChangedKernelHomologyIso :
    (kernel (postnikovExtensionBaseChangeBase R B n b).hom).homology (-(n + 1)) ≅
      B.X.homology (-(n + 1)) :=
  (homologyFunctor (ModuleCat R) (.up ℤ) (-(n + 1))).mapIso
    (postnikovBaseChangedKernelIso R B n b) ≪≫ postnikovKernelHomologyIso R B n

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
