module

public import SerrePositivity.KST.Spectra.RawSpectrumPointedCompositionComparison

/-!
概要：零写像の二つの基点の合成を、元の全写像空間の基点へ同定する。
方針：smash 商の基点保存と点つき合成の基点保存を合成する。
規約：通常の単体集合の射の厳密な等式。使われ方：零評価の零対象経由の因子分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 二つの基点の積は smash 商で smash の基点へ送られる。 -/
lemma basepoint_productToSmash (P Q : PointedSimplicialSet.{u}) :
    (λ_ (𝟙_ SSet.{u})).inv ≫ (P.hom ⊗ₘ Q.hom) ≫
      PointedSimplicialSet.productToSmash P Q = (P ⊗ Q).hom := by
  have h : (λ_ (𝟙_ SSet.{u})).inv ≫ (P.hom ⊗ₘ Q.hom) =
      CartesianMonoidalCategory.lift P.hom Q.hom := rfl
  rw [← Category.assoc, h]
  exact Under.w (PointedObject.smashQuotient P Q)

/-- 元の全写像空間の基点二つの合成は元の基点そのもの。 -/
lemma basepoint_composition (X Y : OmegaSpectrum.{u}) (Z : KanSequence.{u}) :
    (λ_ (𝟙_ SSet.{u})).inv ≫
        ((pointedSpace X Y.toKanSequence).hom ⊗ₘ (pointedSpace Y Z).hom) ≫
          composition X Y Z = (pointedSpace X Z).hom := by
  rw [← productToSmash_pointedComposition]
  have h := congrArg (fun f ↦ f ≫ (pointedComposition X Y Z).right)
    (basepoint_productToSmash (pointedSpace X Y.toKanSequence) (pointedSpace Y Z))
  simpa only [Category.assoc] using h.trans (Under.w (pointedComposition X Y Z))

end SerrePositivity.KST.Spectra.RawSpectrumMapping
