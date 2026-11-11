module

public import SerrePositivity.KST.NonConnective.SequentialRawHomLimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.StrictHomotopyLimits

/-!
概要：逐次 BF 余錐の全 Raw Hom 極限を、元の反対の単体的圏の Hom 錐へ厳密に移す。
方針：元の前合成の全単体の等式により、二つの Hom 関手を同定する。
規約：元の余錐と Hom を取り替えない。
使われ方：相対 cofibrant な列の実 ∞ 余極限判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
local instance sequentialNativeHomSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 元の反対の BF 圏の全 Hom 関手は、同じ Raw Hom 前層そのもの。 -/
lemma sequentialOppositeHomFunctor_eq (Y : OmegaSpectrum.{u}) :
    (SimplicialCategory.sHomFunctor OmegaSpectrum.{u}ᵒᵖ).obj (Opposite.op (Opposite.op Y)) =
      RawSpectrumMapping.sourceFunctor Y.toKanSequence ⋙ PointedSimplicialSet.forget := by
  refine CategoryTheory.Functor.ext
    (F := (SimplicialCategory.sHomFunctor OmegaSpectrum.{u}ᵒᵖ).obj (Opposite.op (Opposite.op Y)))
    (G := RawSpectrumMapping.sourceFunctor Y.toKanSequence ⋙ PointedSimplicialSet.forget)
    (fun _ ↦ rfl) ?_
  intro X Z f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change eHomWhiskerRight SSet f.unop Y = RawSpectrumMapping.pre f.unop Y.toKanSequence
  exact (RawSpectrumMapping.pre_spectrum f.unop Y).symm

/-- 同じ逐次 BF 余錐の、反対の全ての元の豊穣 Hom による錐は通常の極限。 -/
def sequentialNativeHomIsLimit (D : SpectrumSequence.{u}) (Y : OmegaSpectrum.{u}ᵒᵖ) :
    IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone (sequentialLevelColimitCocone D).op Y) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram
  rw [sequentialOppositeHomFunctor_eq]
  exact sequentialRawHomIsLimit D Y.unop.toKanSequence

end SerrePositivity.KST.NonConnective
