module

public import SerrePositivity.KST.LocalizingInvariants.DGDerivationFactorization
public import SerrePositivity.KST.LocalizingInvariants.DGBimoduleImageSupport

/-!
概要：cokernel で消える実 derivation を、構成した実係数像へ制限する。
方針：cokernel の kernel への鎖写像 lift と、単射による derivation 則の降下を合成。
規約：元の classifying 切断への合成式も保持。使われ方：LT Lemma 2.30 の像制限。
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
  (f : M ⟶ N) (d : Derivation A N) (hd : d.hom ≫ cokernel.π f.hom = 0)

def Derivation.restrictImageOfCokernel : Derivation A (DGBimoduleImage.obj f) := by
  have := DGBimoduleImage.inclusion_mono f
  exact d.ofFactorization (DGBimoduleImage.inclusion f)
    (DGBimoduleImage.chainLift f d.hom hd) (DGBimoduleImage.chainLift_inclusion f d.hom hd)

lemma Derivation.restrictImageOfCokernel_map :
    (d.restrictImageOfCokernel f hd).map A (DGBimoduleImage.inclusion f) = d := by
  apply Derivation.ext
  exact DGBimoduleImage.chainLift_inclusion f d.hom hd

lemma Derivation.restrictImageOfCokernel_section :
    (d.restrictImageOfCokernel f hd).section ≫
      coefficientMap A (DGBimoduleImage.inclusion f) = d.section := by
  rw [Derivation.section_map, Derivation.restrictImageOfCokernel_map]

end SerrePositivity.KST.LocalizingInvariants.SquareZero
