module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroCoefficientMap
public import SerrePositivity.KST.LocalizingInvariants.DGBimoduleImage

/-!
概要：係数の単射への鎖写像の因子分解は、実 derivation の因子分解へ一意に上がる。
方針：単位則と Leibniz 則を係数の単射へ合成して証明し、実像にも適用する。
規約：鎖写像の因子分解の存在は別途示す。使われ方：LT の像へ降りる class。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory Preadditive
open scoped MonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] {A : Mon (Complex R)} {M N : Bimod A A}
  (i : M ⟶ N) [Mono i.hom] (d : Derivation A N) (l : A.X ⟶ M.X) (hl : l ≫ i.hom = d.hom)

def Derivation.ofFactorization : Derivation A M where
  hom := l
  unit := by
    apply (cancel_mono i.hom).1
    rw [Category.assoc, hl, d.unit, zero_comp]
  leibniz := by
    apply (cancel_mono i.hom).1
    rw [Category.assoc, hl, d.leibniz, add_comp, Category.assoc, Category.assoc,
      i.left_act_hom, i.right_act_hom, ← whiskerLeft_comp_assoc,
      ← comp_whiskerRight_assoc, hl]

lemma Derivation.ofFactorization_map : (d.ofFactorization i l hl).map A i = d := by
  apply Derivation.ext
  exact hl

lemma Derivation.ofFactorization_section :
    (d.ofFactorization i l hl).section ≫ coefficientMap A i = d.section := by
  rw [Derivation.section_map, Derivation.ofFactorization_map]

lemma Derivation.map_injective : Function.Injective (Derivation.map A i) := by
  intro d₁ d₂ h
  apply Derivation.ext
  apply (cancel_mono i.hom).1
  exact congrArg Derivation.hom h

variable (f : M ⟶ N) (t : A.X ⟶ M.X) (ht : t ≫ f.hom = d.hom)

/-- The coefficient image is constructed; only the chain factorization is input. -/
def Derivation.restrictImage : Derivation A (DGBimoduleImage.obj f) := by
  have := DGBimoduleImage.inclusion_mono f
  exact d.ofFactorization (DGBimoduleImage.inclusion f)
    (t ≫ (DGBimoduleImage.projection f).hom) (by
      rw [Category.assoc]
      exact (congrArg (fun q ↦ t ≫ q.hom)
        (DGBimoduleImage.projection_inclusion f)).trans ht)

lemma Derivation.restrictImage_map :
    (d.restrictImage f t ht).map A (DGBimoduleImage.inclusion f) = d := by
  have := DGBimoduleImage.inclusion_mono f
  apply Derivation.ext
  change (t ≫ (DGBimoduleImage.projection f).hom) ≫
    (DGBimoduleImage.inclusion f).hom = d.hom
  rw [Category.assoc]
  exact (congrArg (fun q ↦ t ≫ q.hom)
    (DGBimoduleImage.projection_inclusion f)).trans ht

end SerrePositivity.KST.LocalizingInvariants.SquareZero
