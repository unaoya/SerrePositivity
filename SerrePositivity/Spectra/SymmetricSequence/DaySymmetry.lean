module

public import SerrePositivity.Spectra.SymmetricSequence.DayMonoidal
public import Mathlib.CategoryTheory.Monoidal.DayConvolution.Braided

/-!
# convolution の対称モノイダル構造

lawful な Day 構造の関手圏への包含を使い、Mathlib の Day braiding を引き戻す。
自然性と二つの hexagon、対称性を包含の忠実性で確認する。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C]

attribute [local instance] LawfulDayConvolutionMonoidalCategoryStruct.convolution
  LawfulDayConvolutionMonoidalCategoryStruct.convolution₂
  LawfulDayConvolutionMonoidalCategoryStruct.convolution₂'

/-- lawful な Day 構造の関手圏への包含。 -/
abbrev dayEmbedding : SymmetricSequence C ⥤ (FiniteBijection ⥤ C) :=
  LawfulDayConvolutionMonoidalCategoryStruct.ι FiniteBijection C (SymmetricSequence C)

instance dayEmbedding_full : (dayEmbedding (C := C)).Full :=
  inferInstanceAs (toFunctorCategory (C := C)).Full

/-- Day braiding を対称列の型へ引き戻した交換同型。 -/
def convolutionBraiding (F G : SymmetricSequence C) : F ⊗ G ≅ G ⊗ F :=
  (Functor.FullyFaithful.ofFullyFaithful dayEmbedding).preimageIso
    (DayConvolution.braiding (dayEmbedding.obj F) (dayEmbedding.obj G))

@[simp] lemma dayEmbedding_map_braiding (F G : SymmetricSequence C) :
    dayEmbedding.map (convolutionBraiding F G).hom =
      (DayConvolution.braiding (dayEmbedding.obj F) (dayEmbedding.obj G)).hom := by
  exact (Functor.FullyFaithful.ofFullyFaithful dayEmbedding).map_preimage _

lemma dayEmbedding_map_associator_inv (F G H : SymmetricSequence C) :
    dayEmbedding.map (α_ F G H).inv =
      (DayConvolution.associator (dayEmbedding.obj F)
        (dayEmbedding.obj G) (dayEmbedding.obj H)).inv := by
  have h : dayEmbedding.mapIso (α_ F G H) =
      DayConvolution.associator (dayEmbedding.obj F)
        (dayEmbedding.obj G) (dayEmbedding.obj H) :=
    Iso.ext (LawfulDayConvolutionMonoidalCategoryStruct.ι_map_associator_hom_eq_associator_hom
      FiniteBijection C (SymmetricSequence C) F G H)
  exact congrArg Iso.inv h

instance convolutionSymmetricCategory : SymmetricCategory (SymmetricSequence C) where
  braiding := convolutionBraiding
  braiding_naturality_right := by
    intro F G H η
    apply (dayEmbedding (C := C)).map_injective
    simp only [Functor.map_comp, dayEmbedding_map_braiding, ← id_tensorHom, ← tensorHom_id,
      LawfulDayConvolutionMonoidalCategoryStruct.ι_map_tensorHom_hom_eq_tensorHom]
    exact DayConvolution.braiding_naturality_right (dayEmbedding.obj F) (dayEmbedding.map η)
  braiding_naturality_left := by
    intro F G η H
    apply (dayEmbedding (C := C)).map_injective
    simp only [Functor.map_comp, dayEmbedding_map_braiding, ← id_tensorHom, ← tensorHom_id,
      LawfulDayConvolutionMonoidalCategoryStruct.ι_map_tensorHom_hom_eq_tensorHom]
    exact DayConvolution.braiding_naturality_left (dayEmbedding.map η) (dayEmbedding.obj H)
  hexagon_forward := by
    intro F G H
    apply (dayEmbedding (C := C)).map_injective
    simp only [Functor.map_comp, dayEmbedding_map_braiding, ← id_tensorHom, ← tensorHom_id,
      LawfulDayConvolutionMonoidalCategoryStruct.ι_map_tensorHom_hom_eq_tensorHom,
      LawfulDayConvolutionMonoidalCategoryStruct.ι_map_associator_hom_eq_associator_hom]
    exact DayConvolution.hexagon_forward _ _ _
  hexagon_reverse := by
    intro F G H
    apply (dayEmbedding (C := C)).map_injective
    simp only [Functor.map_comp, dayEmbedding_map_braiding, ← id_tensorHom, ← tensorHom_id,
      LawfulDayConvolutionMonoidalCategoryStruct.ι_map_tensorHom_hom_eq_tensorHom,
      dayEmbedding_map_associator_inv]
    exact DayConvolution.hexagon_reverse _ _ _
  symmetry := by
    intro F G
    apply (dayEmbedding (C := C)).map_injective
    simp only [Functor.map_comp, dayEmbedding_map_braiding]
    exact DayConvolution.symmetry _ _

end SerrePositivity.SymmetricSequence
