module

public import SerrePositivity.KST.Spectra.Limits.SpectrumFiniteProducts
public import SerrePositivity.KST.Spectra.SpectrumZeroMaps

/-!
概要：元の BF 二項積への射と両軸の厳密な計算。
方針：段ごとの点つき積の射影則を BF 射の外延性で束ねる。
規約：新しい積対象を選び直さない。使われ方：Sp の積分解の実比較射。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.Binary

abbrev obj (X Y : OmegaSpectrum.{u}) := spectrumBinaryProduct X Y
abbrev fst (X Y : OmegaSpectrum.{u}) := spectrumBinaryProductFst X Y
abbrev snd (X Y : OmegaSpectrum.{u}) := spectrumBinaryProductSnd X Y
abbrev lift {X Y A : OmegaSpectrum.{u}} (f : A ⟶ X) (g : A ⟶ Y) :=
  spectrumBinaryProductLift f g

@[reassoc (attr := simp)]
lemma lift_fst {X Y A : OmegaSpectrum.{u}} (f : A ⟶ X) (g : A ⟶ Y) :
    lift f g ≫ fst X Y = f := OmegaSpectrum.Hom.ext (fun _ ↦ PointedObject.prodLift_fst _ _)

@[reassoc (attr := simp)]
lemma lift_snd {X Y A : OmegaSpectrum.{u}} (f : A ⟶ X) (g : A ⟶ Y) :
    lift f g ≫ snd X Y = g := OmegaSpectrum.Hom.ext (fun _ ↦ PointedObject.prodLift_snd _ _)

/-- 元の BF 積への射の厳密な外延性。 -/
lemma lift_ext {X Y A : OmegaSpectrum.{u}} (f g : A ⟶ obj X Y)
    (hfst : f ≫ fst X Y = g ≫ fst X Y)
    (hsnd : f ≫ snd X Y = g ≫ snd X Y) : f = g := by
  apply OmegaSpectrum.Hom.ext
  intro n
  apply PointedObject.prod_hom_ext
  · exact congrArg (fun h => OmegaSpectrum.Hom.app h n) hfst
  · exact congrArg (fun h => OmegaSpectrum.Hom.app h n) hsnd

lemma pre_lift {A B X Y : OmegaSpectrum.{u}} (f : A ⟶ B) (g : B ⟶ X) (h : B ⟶ Y) :
    f ≫ lift g h = lift (f ≫ g) (f ≫ h) := by
  apply lift_ext <;> simp

def inl (X Y : OmegaSpectrum.{u}) : X ⟶ obj X Y := lift (𝟙 X) 0
def inr (X Y : OmegaSpectrum.{u}) : Y ⟶ obj X Y := lift 0 (𝟙 Y)

@[reassoc (attr := simp)]
lemma inl_fst (X Y : OmegaSpectrum.{u}) : inl X Y ≫ fst X Y = 𝟙 X := lift_fst _ _

@[reassoc (attr := simp)]
lemma inl_snd (X Y : OmegaSpectrum.{u}) : inl X Y ≫ snd X Y = 0 := lift_snd _ _

@[reassoc (attr := simp)]
lemma inr_fst (X Y : OmegaSpectrum.{u}) : inr X Y ≫ fst X Y = 0 := lift_fst _ _

@[reassoc (attr := simp)]
lemma inr_snd (X Y : OmegaSpectrum.{u}) : inr X Y ≫ snd X Y = 𝟙 Y := lift_snd _ _

end SerrePositivity.KST.LocalizingInvariants.Binary
