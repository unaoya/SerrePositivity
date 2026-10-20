module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumProductIso
public import SerrePositivity.KST.LocalizingInvariants.SpectrumZeroClass

/-!
概要：実 Sp 積の因子の同値と因子交換は、両軸と射影を保つ。
方針：両射影による h Sp の外延性と元の BF の零射・恒等射を使う。
規約：整数 π 上だけの計算へ弱めない。使われ方：Tamme 分裂の元の包含との整合性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.Binary

@[reassoc (attr := simp)]
lemma ho_inl_fst (X Y : OmegaSpectrum.{u}) : SpectrumHo.hom (inl X Y) ≫
    SpectrumHo.hom (fst X Y) = 𝟙 _ := by
  rw [← SpectrumHo.hom_comp, inl_fst, SpectrumHo.hom_id]

@[reassoc (attr := simp)]
lemma ho_inl_snd (X Y : OmegaSpectrum.{u}) : SpectrumHo.hom (inl X Y) ≫
    SpectrumHo.hom (snd X Y) = 0 := by
  rw [← SpectrumHo.hom_comp, inl_snd, SpectrumHo.hom_zero]

@[reassoc (attr := simp)]
lemma ho_inr_fst (X Y : OmegaSpectrum.{u}) : SpectrumHo.hom (inr X Y) ≫
    SpectrumHo.hom (fst X Y) = 0 := by
  rw [← SpectrumHo.hom_comp, inr_fst, SpectrumHo.hom_zero]

@[reassoc (attr := simp)]
lemma ho_inr_snd (X Y : OmegaSpectrum.{u}) : SpectrumHo.hom (inr X Y) ≫
    SpectrumHo.hom (snd X Y) = 𝟙 _ := by
  rw [← SpectrumHo.hom_comp, inr_snd, SpectrumHo.hom_id]

variable {A B X Y : OmegaSpectrum.{u}}

lemma hoMap_inl (f : SpectrumHo.obj A ⟶ SpectrumHo.obj X)
    (g : SpectrumHo.obj B ⟶ SpectrumHo.obj Y) : SpectrumHo.hom (inl A B) ≫ hoMap f g =
      f ≫ SpectrumHo.hom (inl X Y) := by
  apply ho_hom_ext
  · rw [Category.assoc, hoMap_fst f g, ← Category.assoc,
      ho_inl_fst A B, Category.id_comp, Category.assoc, ho_inl_fst X Y, Category.comp_id]
  · rw [Category.assoc, hoMap_snd f g, ← Category.assoc,
      ho_inl_snd A B, zero_comp, Category.assoc, ho_inl_snd X Y, comp_zero]

lemma hoMap_inr (f : SpectrumHo.obj A ⟶ SpectrumHo.obj X)
    (g : SpectrumHo.obj B ⟶ SpectrumHo.obj Y) : SpectrumHo.hom (inr A B) ≫ hoMap f g =
      g ≫ SpectrumHo.hom (inr X Y) := by
  apply ho_hom_ext
  · rw [Category.assoc, hoMap_fst f g, ← Category.assoc,
      ho_inr_fst A B, zero_comp, Category.assoc, ho_inr_fst X Y, comp_zero]
  · rw [Category.assoc, hoMap_snd f g, ← Category.assoc,
      ho_inr_snd A B, Category.id_comp, Category.assoc, ho_inr_snd X Y, Category.comp_id]

lemma swapIso_inl (X Y : OmegaSpectrum.{u}) :
    SpectrumHo.hom (inl X Y) ≫ (swapIso X Y).hom = SpectrumHo.hom (inr Y X) := by
  apply ho_hom_ext
  · change (_ ≫ hoLift _ _) ≫ _ = _
    rw [Category.assoc, hoLift_fst (SpectrumHo.hom (snd X Y))
      (SpectrumHo.hom (fst X Y)), ho_inl_snd X Y, ho_inr_fst Y X]
  · change (_ ≫ hoLift _ _) ≫ _ = _
    rw [Category.assoc, hoLift_snd (SpectrumHo.hom (snd X Y))
      (SpectrumHo.hom (fst X Y)), ho_inl_fst X Y, ho_inr_snd Y X]

lemma swapIso_inr (X Y : OmegaSpectrum.{u}) :
    SpectrumHo.hom (inr X Y) ≫ (swapIso X Y).hom = SpectrumHo.hom (inl Y X) := by
  apply ho_hom_ext
  · change (_ ≫ hoLift _ _) ≫ _ = _
    rw [Category.assoc, hoLift_fst (SpectrumHo.hom (snd X Y))
      (SpectrumHo.hom (fst X Y)), ho_inr_snd X Y, ho_inl_fst Y X]
  · change (_ ≫ hoLift _ _) ≫ _ = _
    rw [Category.assoc, hoLift_snd (SpectrumHo.hom (snd X Y))
      (SpectrumHo.hom (fst X Y)), ho_inr_fst X Y, ho_inl_snd Y X]

@[reassoc (attr := simp)]
lemma swapIso_fst (X Y : OmegaSpectrum.{u}) : (swapIso X Y).hom ≫ SpectrumHo.hom (fst Y X) =
    SpectrumHo.hom (snd X Y) := hoLift_fst _ _

@[reassoc (attr := simp)]
lemma swapIso_snd (X Y : OmegaSpectrum.{u}) : (swapIso X Y).hom ≫ SpectrumHo.hom (snd Y X) =
    SpectrumHo.hom (fst X Y) := hoLift_snd _ _

lemma mapIso_swap_snd (e : SpectrumHo.obj A ≅ SpectrumHo.obj X)
    (d : SpectrumHo.obj B ≅ SpectrumHo.obj Y) :
    (mapIso e d ≪≫ swapIso X Y).hom ≫ SpectrumHo.hom (snd Y X) =
      SpectrumHo.hom (fst A B) ≫ e.hom := by
  change (hoMap e.hom d.hom ≫ (swapIso X Y).hom) ≫ _ = _
  rw [Category.assoc, swapIso_snd X Y, hoMap_fst e.hom d.hom]

end SerrePositivity.KST.LocalizingInvariants.Binary
