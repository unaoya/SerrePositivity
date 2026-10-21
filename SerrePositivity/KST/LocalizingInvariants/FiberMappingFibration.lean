module

public import SerrePositivity.KST.LocalizingInvariants.FiberMappingAnodyneFamily
public import SerrePositivity.KST.Spectra.RawSpectrumMappingLaws

/-!
概要：段ごとの Kan fibration は、cofibrant BF 源からの全写像空間でも Kan fibration。
方針：整合した anodyne 族を全写像空間へ持ち上げ、二つの比較式を段で確認する。
規約：全単射への RLP や同値性は要求しない。使われ方：coherent 正方形の相対厳密化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.FiberMapping
open RawSpectrumMapping

lemma post_anodyne_lifting (X : OmegaSpectrum.{u}) {Y Z : KanSequence.{u}}
    (p : KanSequence.Hom Y Z) (hp : ∀ n, Fibration (p.app n).right)
    {T U : SSet.{u}} (j : T ⟶ U) (hj : anodyneExtensions j) :
    HasLiftingProperty j (post X p) := by
  constructor
  intro a b sq
  obtain ⟨f, ha, hb, hf⟩ := anodyneFamily X p hp j hj a b sq.w
  let l := lift X Y f hf
  have hl (n : ℕ) : l ≫ evaluation X Y n = f n := lift_evaluation _ _ _ _ n
  refine ⟨⟨{ l := l, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply hom_ext X Y
    intro n
    rw [Category.assoc, hl]
    exact ha n
  · apply hom_ext X Z
    intro n
    rw [Category.assoc, post_evaluation X p n, ← Category.assoc, hl]
    exact hb n

lemma post_fibration (X : OmegaSpectrum.{u}) {Y Z : KanSequence.{u}}
    (p : KanSequence.Hom Y Z) (hp : ∀ n, Fibration (p.app n).right) :
    Fibration (post X p) := by
  rw [fibration_iff]
  intro T U j hj
  apply post_anodyne_lifting X p hp j
  rw [anodyneExtensions_eq_llp_rlp]
  exact MorphismProperty.le_llp_rlp J _ hj

local instance fiberMappingSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

lemma spectrumPost_fibration (X : OmegaSpectrum.{u}) {Y Z : OmegaSpectrum.{u}}
    (p : Y ⟶ Z) (hp : ∀ n, Fibration (p.app n).right) :
    Fibration (((SimplicialCategory.sHomFunctor OmegaSpectrum.{u}).obj
      (Opposite.op X)).map p) := by
  rw [← post_spectrum X p]
  exact post_fibration X _ hp

end SerrePositivity.KST.LocalizingInvariants.FiberMapping
