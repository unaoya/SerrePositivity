module

public import SerrePositivity.KST.LocalizingInvariants.DGDerivationSectionEquiv

/-!
概要：実双加群の射が誘導する平方零代数射と、derivation の係数移送を構成する。
方針：直和の対角射を使い、左右作用の保存から単位・積・Leibniz 則を得る。
規約：係数射は実 dg 双加群射。使われ方：係数の像へ制限した拡大との比較。
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
variable {R : Type u} [CommRing R] (A : Mon (Complex R)) {M N : Bimod A A} (f : M ⟶ N)

def coefficientMap : algebra A M ⟶ algebra A N := by
  refine Mon.Hom.mk' (biprod.map (𝟙 A.X) f.hom) ?_ ?_
  · change (η[A.X] ≫ biprod.inl) ≫ biprod.map (𝟙 A.X) f.hom = η[A.X] ≫ biprod.inl
    rw [Category.assoc, biprod.inl_map, Category.id_comp]
  · change _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul A M ≫ biprod.map (𝟙 A.X) f.hom =
      (biprod.map (𝟙 A.X) f.hom ⊗ₘ biprod.map (𝟙 A.X) f.hom) ≫ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul A N
    apply biprodTensor_hom_ext
    all_goals
      simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_ll, _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_lr, _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_rl, _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_rr, Category.assoc,
        biprod.inl_map, biprod.inr_map, tensorHom_comp_tensorHom_assoc,
        Category.id_comp, ← whiskerLeft_comp_tensorHom_assoc,
        ← whiskerRight_comp_tensorHom_assoc, _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_ll_assoc, _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_lr_assoc, _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_rl_assoc,
        _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_rr_assoc, MonoidalPreadditive.zero_tensor, MonoidalPreadditive.tensor_zero,
        zero_comp, comp_zero, f.left_act_hom_assoc, f.right_act_hom_assoc]

def Derivation.map (d : Derivation A M) : Derivation A N where
  hom := d.hom ≫ f.hom
  unit := by rw [← Category.assoc, d.unit, zero_comp]
  leibniz := by
    rw [← Category.assoc, d.leibniz, add_comp]
    simp only [Category.assoc, f.left_act_hom, f.right_act_hom,
      ← whiskerLeft_comp_assoc, ← comp_whiskerRight_assoc]

lemma coefficientMap_projection : coefficientMap A f ≫ projection A N = projection A M := by
  apply Mon.Hom.ext
  exact (biprod.map_fst _ _).trans (Category.comp_id _)

lemma Derivation.section_map (d : Derivation A M) :
    d.section ≫ coefficientMap A f = (d.map A f).section := by
  apply Mon.Hom.ext
  change biprod.lift (𝟙 A.X) d.hom ≫ biprod.map (𝟙 A.X) f.hom =
    biprod.lift (𝟙 A.X) (d.hom ≫ f.hom)
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, Category.comp_id, biprod.lift_fst]
  · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc, biprod.lift_snd]

end SerrePositivity.KST.LocalizingInvariants.SquareZero
