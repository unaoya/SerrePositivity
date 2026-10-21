module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumBinaryMaps

/-!
概要：元の BF 二項積の射への厳密な作用。
方針：元の二射影と組を使い、両射影の外延性で恒等・合成を検証する。
規約：Hom の類に落とさない。使われ方：二脚の積射の分解と pullback の貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.Binary
variable {A B C D E F : OmegaSpectrum.{u}}

def map (f : A ⟶ C) (g : B ⟶ D) : obj A B ⟶ obj C D :=
  lift (fst A B ≫ f) (snd A B ≫ g)

@[reassoc (attr := simp)]
lemma map_fst (f : A ⟶ C) (g : B ⟶ D) : map f g ≫ fst C D = fst A B ≫ f :=
  lift_fst _ _

@[reassoc (attr := simp)]
lemma map_snd (f : A ⟶ C) (g : B ⟶ D) : map f g ≫ snd C D = snd A B ≫ g :=
  lift_snd _ _

lemma map_id (A B : OmegaSpectrum.{u}) : map (𝟙 A) (𝟙 B) = 𝟙 (obj A B) := by
  apply lift_ext <;> simp

lemma map_comp (f : A ⟶ C) (g : B ⟶ D) (f' : C ⟶ E) (g' : D ⟶ F) :
    map f g ≫ map f' g' = map (f ≫ f') (g ≫ g') := by
  apply lift_ext <;> simp [Category.assoc]

lemma map_factor (f : A ⟶ C) (g : B ⟶ D) :
    map f g = map f (𝟙 B) ≫ map (𝟙 C) g := by
  rw [map_comp, Category.comp_id, Category.id_comp]

end SerrePositivity.KST.LocalizingInvariants.Binary
