module

public import SerrePositivity.KST.LocalizingInvariants.DGDerivationImageRestriction
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackMap

/-!
概要：像へ制限した derivation の実経路拡大から、元の拡大への代数射を構成する。
方針：classifying 切断と零切断の可換式を、cospan の模型射に使う。
規約：底への二脚と元の乗法的経路を保持。使われ方：LT の像制限後の拡大比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] {A : Mon (Complex R)} {M N : Bimod A A}

lemma zeroSection_coefficientMap (i : M ⟶ N) :
    zeroSection A M ≫ coefficientMap A i = zeroSection A N := by
  apply Mon.Hom.ext
  change biprod.inl ≫ biprod.map (𝟙 A.X) i.hom = biprod.inl
  rw [biprod.inl_map, Category.id_comp]

def Derivation.extension (d : Derivation A N) : Mon (Complex R) :=
  DGAlgebra.HomotopyPullbackModel.algebra R d.section (zeroSection A N)

variable (f : M ⟶ N) (d : Derivation A N) (hd : d.hom ≫ cokernel.π f.hom = 0)

def Derivation.imageExtensionMap : (d.restrictImageOfCokernel f hd).extension ⟶ d.extension :=
  DGAlgebra.HomotopyPullbackModel.map R _ _ _ _ (𝟙 A)
    (coefficientMap A (DGBimoduleImage.inclusion f)) (𝟙 A)
    (by rw [Category.id_comp, Derivation.restrictImageOfCokernel_section])
    (by rw [Category.id_comp, zeroSection_coefficientMap])

lemma Derivation.imageExtensionMap_left : d.imageExtensionMap f hd ≫
    DGAlgebra.HomotopyPullbackModel.left R _ _ =
      DGAlgebra.HomotopyPullbackModel.left R _ _ := by
  exact (DGAlgebra.HomotopyPullbackModel.map_left R _ _ _ _ _ _ _ _ _).trans
    (Category.comp_id _)

lemma Derivation.imageExtensionMap_right : d.imageExtensionMap f hd ≫
    DGAlgebra.HomotopyPullbackModel.right R _ _ =
      DGAlgebra.HomotopyPullbackModel.right R _ _ := by
  exact (DGAlgebra.HomotopyPullbackModel.map_right R _ _ _ _ _ _ _ _ _).trans
    (Category.comp_id _)

lemma Derivation.imageExtensionMap_path : d.imageExtensionMap f hd ≫
    DGAlgebra.HomotopyPullbackModel.path R _ _ =
      DGAlgebra.HomotopyPullbackModel.path R _ _ ≫
        DGAlgebra.Path.map R (coefficientMap A (DGBimoduleImage.inclusion f)) :=
  DGAlgebra.HomotopyPullbackModel.map_path R _ _ _ _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.SquareZero
