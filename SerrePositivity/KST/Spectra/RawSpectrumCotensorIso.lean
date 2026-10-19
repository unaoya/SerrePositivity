module

public import SerrePositivity.KST.Spectra.RawSpectrumCotensorInverse

/-!
概要：任意の cotensor と、整合写像空間全体の内部 Hom の厳密な交換同型。
方針：各段の源交換の順・逆射を普遍射へまとめ、両合成を各段評価で検査する。
規約：全単体次数の点つき同型。使われ方：Sp の native な loop と BF cotensor の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 全写像空間を標的とする内部 Hom の射は、全ての内部 Hom の段評価で決まる。 -/
lemma ihom_pointed_hom_ext (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (A : PointedSimplicialSet.{u}) {T : PointedSimplicialSet.{u}}
    {f g : T ⟶ (ihom A).obj (pointedSpace X Y)}
    (h : ∀ n, f ≫ (ihom A).map (pointedEvaluation X Y n) =
      g ≫ (ihom A).map (pointedEvaluation X Y n)) : f = g := by
  apply uncurry_injective
  apply pointed_hom_ext X Y
  intro n
  apply curry_injective
  rw [curry_natural_right, curry_natural_right, curry_uncurry, curry_uncurry]
  exact h n

/-- 二つの比較を順に行うと cotensor 値への元の整合写像へ戻る。 -/
lemma cotensorComparison_inverse (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (A : PointedSimplicialSet.{u}) :
    cotensorComparison X Y A ≫ cotensorInverse X Y A =
      𝟙 (pointedSpace X (KanSequence.mapping A Y)) := by
  apply pointed_hom_ext X (KanSequence.mapping A Y)
  intro n
  rw [Category.assoc, cotensorInverse_evaluation, Category.id_comp]
  dsimp only [inverseExchangeFamily]
  rw [← Category.assoc, cotensorComparison_evaluation]
  dsimp only [exchangeFamily]
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 逆の順の二比較も全写像空間の内部 Hom の恒等射。 -/
lemma cotensorInverse_comparison (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (A : PointedSimplicialSet.{u}) :
    cotensorInverse X Y A ≫ cotensorComparison X Y A =
      𝟙 ((ihom A).obj (pointedSpace X Y)) := by
  apply ihom_pointed_hom_ext X Y A
  intro n
  rw [Category.assoc, cotensorComparison_evaluation, Category.id_comp]
  dsimp only [exchangeFamily]
  rw [← Category.assoc, cotensorInverse_evaluation]
  dsimp only [inverseExchangeFamily]
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 整合写像空間と任意の点つき cotensor の厳密な交換同型。 -/
def cotensorIso (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) (A : PointedSimplicialSet.{u}) :
    pointedSpace X (KanSequence.mapping A Y) ≅ (ihom A).obj (pointedSpace X Y) where
  hom := cotensorComparison X Y A
  inv := cotensorInverse X Y A
  hom_inv_id := cotensorComparison_inverse X Y A
  inv_hom_id := cotensorInverse_comparison X Y A

end SerrePositivity.KST.Spectra.RawSpectrumMapping
