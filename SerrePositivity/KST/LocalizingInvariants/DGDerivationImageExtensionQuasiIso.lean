module

public import SerrePositivity.KST.LocalizingInvariants.DGDerivationImageExtension
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackMapQuasiIso

/-!
概要：係数像の包含が準同型なら、構成した像制限拡大の比較射も準同型である。
方針：平方零代数の係数比較を直和で計算し、三成分の模型比較定理を適用する。
規約：像包含の準同型性は明示的な条件。使われ方：LT のレベル比較の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] {A : Mon (Complex R)} {M N : Bimod A A}
  (f : M ⟶ N) (d : Derivation A N) (hd : d.hom ≫ cokernel.π f.hom = 0)

lemma Derivation.imageExtensionMap_quasiIso
    (hf : QuasiIso (DGBimoduleImage.inclusion f).hom) :
    QuasiIso (d.imageExtensionMap f hd).hom := by
  have hb : QuasiIso (coefficientMap A (DGBimoduleImage.inclusion f)).hom := by
    change QuasiIso (biprod.map (𝟙 A.X) (DGBimoduleImage.inclusion f).hom)
    exact cochainBiprodMap_quasiIso _ _ (quasiIso_of_isIso _) hf
  exact DGAlgebra.HomotopyPullbackModel.map_quasiIso R _ _ _ _ _ _ _ _ _
    (quasiIso_of_isIso (𝟙 A.X)) hb (quasiIso_of_isIso (𝟙 A.X))

end SerrePositivity.KST.LocalizingInvariants.SquareZero
