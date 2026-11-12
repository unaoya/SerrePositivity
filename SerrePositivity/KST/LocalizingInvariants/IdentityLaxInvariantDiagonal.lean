module

public import SerrePositivity.KST.LocalizingInvariants.IdentityLaxDiagonal
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxVerdierProductMap
public import SerrePositivity.KST.LocalizingInvariants.InvariantZeroMap

/-!
概要：恒等矢印の値は実積の対角となり、積からの差との合成は h Sp で零。
方針：両射影の厳密等式を値へ写し、全値が零となる差を零保存で処理する。
規約：π の一致から射の一致を推論しない。使われ方：E(Σ) の整数 π の負号。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.IdentityLax
variable (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u}) (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u})

lemma valueDiagonal_fst :
    SpectrumHo.hom (valueMap Φ (exactDiagonal A)) ≫
      SpectrumHo.hom (valueMap Φ (laxFst (𝟙 A) (𝟙 A))) = 𝟙 _ := by
  have h : (exactDiagonal A : A ⟶ laxCategory (𝟙 A) (𝟙 A)) ≫
      laxFst (𝟙 A) (𝟙 A) = 𝟙 A := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext (diagonal_fst A)
  change (stableValueFunctor Φ).map (exactDiagonal A) ≫
    (stableValueFunctor Φ).map (laxFst (𝟙 A) (𝟙 A)) = _
  rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_id]
  rfl

lemma valueDiagonal_snd :
    SpectrumHo.hom (valueMap Φ (exactDiagonal A)) ≫
      SpectrumHo.hom (valueMap Φ (laxSnd (𝟙 A) (𝟙 A))) = 𝟙 _ := by
  have h : (exactDiagonal A : A ⟶ laxCategory (𝟙 A) (𝟙 A)) ≫
      laxSnd (𝟙 A) (𝟙 A) = 𝟙 A := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext (diagonal_snd A)
  change (stableValueFunctor Φ).map (exactDiagonal A) ≫
    (stableValueFunctor Φ).map (laxSnd (𝟙 A) (𝟙 A)) = _
  rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_id]
  rfl

variable {Φ} (hΦ : IsLocalizingInvariant Φ)

lemma valueDiagonal_product :
    SpectrumHo.hom (valueMap Φ (exactDiagonal A)) ≫
      (hΦ.tammeProjectionEquivalence (𝟙 A) (𝟙 A)).hom =
        SpectrumHo.hom (Binary.lift (𝟙 (value Φ A)) (𝟙 (value Φ A))) := by
  apply Binary.ho_hom_ext
  · rw [Category.assoc, IsLocalizingInvariant.tammeProjectionEquivalence_fst,
      valueDiagonal_fst, ← SpectrumHo.hom_comp, Binary.lift_fst, SpectrumHo.hom_id]
  · rw [Category.assoc, IsLocalizingInvariant.tammeProjectionEquivalence_snd,
      valueDiagonal_snd, ← SpectrumHo.hom_comp, Binary.lift_snd, SpectrumHo.hom_id]

include hΦ in
lemma valueDiagonal_difference_zero :
    SpectrumHo.hom (valueMap Φ (exactDiagonal A)) ≫
      SpectrumHo.hom (valueMap Φ (exactLaxDifference (𝟙 A) (𝟙 A))) = 0 := by
  let f : A ⟶ A := exactDiagonal A ≫ exactLaxDifference (𝟙 A) (𝟙 A)
  have hz := hΦ.valueMap_hom_zero_of_zero_values f (difference_diagonal_zero A)
  change (stableValueFunctor Φ).map (exactDiagonal A) ≫
    (stableValueFunctor Φ).map (exactLaxDifference (𝟙 A) (𝟙 A)) = 0
  rw [← CategoryTheory.Functor.map_comp]
  exact hz

lemma productDiagonal_difference_zero :
    SpectrumHo.hom (Binary.lift (𝟙 (value Φ A)) (𝟙 (value Φ A))) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProjectionDifferenceHom hΦ) (𝟙 A) (𝟙 A)
        (exactLaxDifference (𝟙 A) (𝟙 A)) = 0 := by
  rw [← valueDiagonal_product A hΦ, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProjectionDifferenceHom,
    Category.assoc, Iso.hom_inv_id_assoc]
  exact valueDiagonal_difference_zero A hΦ

end SerrePositivity.KST.LocalizingInvariants.IdentityLax
