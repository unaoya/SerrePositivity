module

public import SerrePositivity.KST.LocalizingInvariants.BinaryMappingExt
public import SerrePositivity.KST.LocalizingInvariants.SpectrumHomotopyFunctor

/-!
概要：元の BF 二項積の因子の Sp 同値を、実積対象の Sp 同値へ移す。
方針：h Sp の射を元の BF 射で表し、両射影の普遍性で合成則を証明する。
規約：単なる整数 π の群の積を使わない。使われ方：K-8 の積因子の元の値への同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.Binary

variable {A B X Y : OmegaSpectrum.{u}}

lemma ho_hom_ext (f g : SpectrumHo.obj A ⟶ SpectrumHo.obj (obj X Y))
    (hfst : f ≫ SpectrumHo.hom (fst X Y) = g ≫ SpectrumHo.hom (fst X Y))
    (hsnd : f ≫ SpectrumHo.hom (snd X Y) = g ≫ SpectrumHo.hom (snd X Y)) : f = g := by
  obtain ⟨a, rfl⟩ := SpectrumHo.exists_representative f
  obtain ⟨b, rfl⟩ := SpectrumHo.exists_representative g
  exact hom_ext a b hfst hsnd

def hoLift (f : SpectrumHo.obj A ⟶ SpectrumHo.obj X)
    (g : SpectrumHo.obj A ⟶ SpectrumHo.obj Y) : SpectrumHo.obj A ⟶ SpectrumHo.obj (obj X Y) :=
  SpectrumHo.hom (lift (SpectrumHo.representative f) (SpectrumHo.representative g))

@[reassoc (attr := simp)]
lemma hoLift_fst (f : SpectrumHo.obj A ⟶ SpectrumHo.obj X)
    (g : SpectrumHo.obj A ⟶ SpectrumHo.obj Y) : hoLift f g ≫ SpectrumHo.hom (fst X Y) = f := by
  rw [hoLift, ← SpectrumHo.hom_comp, lift_fst, SpectrumHo.hom_representative]

@[reassoc (attr := simp)]
lemma hoLift_snd (f : SpectrumHo.obj A ⟶ SpectrumHo.obj X)
    (g : SpectrumHo.obj A ⟶ SpectrumHo.obj Y) : hoLift f g ≫ SpectrumHo.hom (snd X Y) = g := by
  rw [hoLift, ← SpectrumHo.hom_comp, lift_snd, SpectrumHo.hom_representative]

def hoMap (f : SpectrumHo.obj A ⟶ SpectrumHo.obj X)
    (g : SpectrumHo.obj B ⟶ SpectrumHo.obj Y) :
    SpectrumHo.obj (obj A B) ⟶ SpectrumHo.obj (obj X Y) :=
  hoLift (SpectrumHo.hom (fst A B) ≫ f) (SpectrumHo.hom (snd A B) ≫ g)

@[reassoc (attr := simp)]
lemma hoMap_fst (f : SpectrumHo.obj A ⟶ SpectrumHo.obj X)
    (g : SpectrumHo.obj B ⟶ SpectrumHo.obj Y) :
    hoMap f g ≫ SpectrumHo.hom (fst X Y) = SpectrumHo.hom (fst A B) ≫ f := hoLift_fst _ _

@[reassoc (attr := simp)]
lemma hoMap_snd (f : SpectrumHo.obj A ⟶ SpectrumHo.obj X)
    (g : SpectrumHo.obj B ⟶ SpectrumHo.obj Y) :
    hoMap f g ≫ SpectrumHo.hom (snd X Y) = SpectrumHo.hom (snd A B) ≫ g := hoLift_snd _ _

/-- 因子の元の Sp の同値から、元の実 ∞ 積の頂点間の同値を得る。 -/
def mapIso (e : SpectrumHo.obj A ≅ SpectrumHo.obj X) (d : SpectrumHo.obj B ≅ SpectrumHo.obj Y) :
    SpectrumHo.obj (obj A B) ≅ SpectrumHo.obj (obj X Y) where
  hom := hoMap e.hom d.hom
  inv := hoMap e.inv d.inv
  hom_inv_id := by
    apply ho_hom_ext <;> simp only [Category.assoc, hoMap_fst, hoMap_snd, Category.id_comp]
    · rw [← Category.assoc, hoMap_fst, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · rw [← Category.assoc, hoMap_snd, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  inv_hom_id := by
    apply ho_hom_ext <;> simp only [Category.assoc, hoMap_fst, hoMap_snd, Category.id_comp]
    · rw [← Category.assoc, hoMap_fst, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · rw [← Category.assoc, hoMap_snd, Category.assoc, Iso.inv_hom_id, Category.comp_id]

def swapIso (X Y : OmegaSpectrum.{u}) : SpectrumHo.obj (obj X Y) ≅ SpectrumHo.obj (obj Y X) where
  hom := hoLift (SpectrumHo.hom (snd X Y)) (SpectrumHo.hom (fst X Y))
  inv := hoLift (SpectrumHo.hom (snd Y X)) (SpectrumHo.hom (fst Y X))
  hom_inv_id := by
    apply ho_hom_ext
    · rw [Category.assoc, hoLift_fst (SpectrumHo.hom (snd Y X))
        (SpectrumHo.hom (fst Y X)), hoLift_snd, Category.id_comp]
    · rw [Category.assoc, hoLift_snd (SpectrumHo.hom (snd Y X))
        (SpectrumHo.hom (fst Y X)), hoLift_fst, Category.id_comp]
  inv_hom_id := by
    apply ho_hom_ext
    · rw [Category.assoc, hoLift_fst (SpectrumHo.hom (snd X Y))
        (SpectrumHo.hom (fst X Y)), hoLift_snd, Category.id_comp]
    · rw [Category.assoc, hoLift_snd (SpectrumHo.hom (snd X Y))
        (SpectrumHo.hom (fst X Y)), hoLift_fst, Category.id_comp]

end SerrePositivity.KST.LocalizingInvariants.Binary
