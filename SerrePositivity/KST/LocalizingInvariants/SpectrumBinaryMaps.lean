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

open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.Binary

abbrev obj (X Y : OmegaSpectrum.{u}) := _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumBinaryProduct X Y
abbrev fst (X Y : OmegaSpectrum.{u}) := _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumBinaryProductFst X Y
abbrev snd (X Y : OmegaSpectrum.{u}) := _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumBinaryProductSnd X Y
abbrev lift {X Y A : OmegaSpectrum.{u}} (f : A ⟶ X) (g : A ⟶ Y) :=
  _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumBinaryProductLift f g

@[reassoc (attr := simp)]
lemma lift_fst {X Y A : OmegaSpectrum.{u}} (f : A ⟶ X) (g : A ⟶ Y) :
    _root_.SerrePositivity.KST.LocalizingInvariants.Binary.lift f g ≫ _root_.SerrePositivity.KST.LocalizingInvariants.Binary.fst X Y = f := OmegaSpectrum.Hom.ext (fun _ ↦ PointedObject.prodLift_fst _ _)

@[reassoc (attr := simp)]
lemma lift_snd {X Y A : OmegaSpectrum.{u}} (f : A ⟶ X) (g : A ⟶ Y) :
    _root_.SerrePositivity.KST.LocalizingInvariants.Binary.lift f g ≫ _root_.SerrePositivity.KST.LocalizingInvariants.Binary.snd X Y = g := OmegaSpectrum.Hom.ext (fun _ ↦ PointedObject.prodLift_snd _ _)

/-- 元の BF 積への射の厳密な外延性。 -/
lemma lift_ext {X Y A : OmegaSpectrum.{u}} (f g : A ⟶ _root_.SerrePositivity.KST.LocalizingInvariants.Binary.obj X Y)
    (hfst : f ≫ _root_.SerrePositivity.KST.LocalizingInvariants.Binary.fst X Y = g ≫ _root_.SerrePositivity.KST.LocalizingInvariants.Binary.fst X Y)
    (hsnd : f ≫ _root_.SerrePositivity.KST.LocalizingInvariants.Binary.snd X Y = g ≫ _root_.SerrePositivity.KST.LocalizingInvariants.Binary.snd X Y) : f = g := by
  apply OmegaSpectrum.Hom.ext
  intro n
  apply PointedObject.prod_hom_ext
  · exact congrArg (fun h => OmegaSpectrum.Hom.app h n) hfst
  · exact congrArg (fun h => OmegaSpectrum.Hom.app h n) hsnd

lemma pre_lift {A B X Y : OmegaSpectrum.{u}} (f : A ⟶ B) (g : B ⟶ X) (h : B ⟶ Y) :
    f ≫ _root_.SerrePositivity.KST.LocalizingInvariants.Binary.lift g h = _root_.SerrePositivity.KST.LocalizingInvariants.Binary.lift (f ≫ g) (f ≫ h) := by
  apply _root_.SerrePositivity.KST.LocalizingInvariants.Binary.lift_ext <;> simp

def inl (X Y : OmegaSpectrum.{u}) : X ⟶ _root_.SerrePositivity.KST.LocalizingInvariants.Binary.obj X Y := _root_.SerrePositivity.KST.LocalizingInvariants.Binary.lift (𝟙 X) 0
def inr (X Y : OmegaSpectrum.{u}) : Y ⟶ _root_.SerrePositivity.KST.LocalizingInvariants.Binary.obj X Y := _root_.SerrePositivity.KST.LocalizingInvariants.Binary.lift 0 (𝟙 Y)

@[reassoc (attr := simp)]
lemma inl_fst (X Y : OmegaSpectrum.{u}) : inl X Y ≫ _root_.SerrePositivity.KST.LocalizingInvariants.Binary.fst X Y = 𝟙 X := _root_.SerrePositivity.KST.LocalizingInvariants.Binary.lift_fst _ _

@[reassoc (attr := simp)]
lemma inl_snd (X Y : OmegaSpectrum.{u}) : inl X Y ≫ _root_.SerrePositivity.KST.LocalizingInvariants.Binary.snd X Y = 0 := _root_.SerrePositivity.KST.LocalizingInvariants.Binary.lift_snd _ _

@[reassoc (attr := simp)]
lemma inr_fst (X Y : OmegaSpectrum.{u}) : inr X Y ≫ _root_.SerrePositivity.KST.LocalizingInvariants.Binary.fst X Y = 0 := _root_.SerrePositivity.KST.LocalizingInvariants.Binary.lift_fst _ _

@[reassoc (attr := simp)]
lemma inr_snd (X Y : OmegaSpectrum.{u}) : inr X Y ≫ _root_.SerrePositivity.KST.LocalizingInvariants.Binary.snd X Y = 𝟙 Y := _root_.SerrePositivity.KST.LocalizingInvariants.Binary.lift_snd _ _

end SerrePositivity.KST.LocalizingInvariants.Binary
