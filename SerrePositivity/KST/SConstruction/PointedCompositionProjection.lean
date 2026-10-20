module
public import SerrePositivity.KST.SConstruction.SpectrumFixedFactorEvaluation

/-! # 元の豊穣合成と raw 段射影の可換性
概要：元の二つの全 Hom 族の合成を、最終標的の射による後合成へ厳密に移す。
方針：点つき豊穣合成の後合成則を、同じ二族の射対に制限する。
規約：全パラメータの実写像の等式を使い、頂点の等式で代用しない。
使われ方：元の BF whisker の全段を、補正後の raw 交換辺へ照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open scoped Simplicial
local instance compositionProjectionPointedSimplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
local instance compositionProjectionSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 元の二つの全族を合成して後合成する写像は、後続族を後合成してからの同じ合成。 -/
lemma pointedComposition_post {U : SSet.{u}} {A B C D : PointedSimplicialSet.{u}}
    (a : U ⟶ (PointedObject.basedHom A B).right)
    (b : U ⟶ (PointedObject.basedHom B C).right) (p : C ⟶ D) :
    (lift a b ≫ eComp SSet A B C) ≫ (PointedObject.basedHomMap A p).right =
      lift a (b ≫ (PointedObject.basedHomMap B p).right) ≫ eComp SSet A B D := by
  rw [Category.assoc, ← PointedEnrichment.whiskerLeft_eq, eComp_eHomWhiskerLeft,
    ← Category.assoc, PointedEnrichment.whiskerLeft_eq]
  congr 1

/-- 固定最終 BF 射の全合成を段射影すると、同じ段の元の射影済み終端との合成。 -/
lemma spectrumFixedRightComposition_post_evaluation {W Y Z : OmegaSpectrum.{u}}
    (h : Y ⟶ Z) (n : ℕ) {D : PointedSimplicialSet.{u}} (p : (Z.level n).space ⟶ D) :
    enrichedFixedRightComposition (W := W) h ≫ OmegaSpectrum.evaluation W Z n ≫
        (PointedObject.basedHomMap (W.level n).space p).right =
      OmegaSpectrum.evaluation W Y n ≫
        lift (𝟙 _) (SSet.const ((OmegaSpectrum.evaluation Y Z n).app (Opposite.op ⦋0⦌)
          (SimplicialCategory.homEquiv' _ _ h)) ≫
            (PointedObject.basedHomMap (Y.level n).space p).right) ≫
              eComp SSet (W.level n).space (Y.level n).space D := by
  rw [← Category.assoc, spectrumFixedRightComposition_evaluation]
  simpa only [Category.assoc] using
    congrArg (OmegaSpectrum.evaluation W Y n ≫ ·)
      (pointedComposition_post (𝟙 _)
        (SSet.const ((OmegaSpectrum.evaluation Y Z n).app (Opposite.op ⦋0⦌)
          (SimplicialCategory.homEquiv' _ _ h))) p)

/-- 固定第一 BF 射の全合成の段射影も、同じ元の後続族の射影との合成。 -/
lemma spectrumFixedLeftComposition_post_evaluation {W X Z : OmegaSpectrum.{u}}
    (f : W ⟶ X) (n : ℕ) {D : PointedSimplicialSet.{u}} (p : (Z.level n).space ⟶ D) :
    enrichedFixedLeftComposition (Z := Z) f ≫ OmegaSpectrum.evaluation W Z n ≫
        (PointedObject.basedHomMap (W.level n).space p).right =
      OmegaSpectrum.evaluation X Z n ≫
        lift (SSet.const ((OmegaSpectrum.evaluation W X n).app (Opposite.op ⦋0⦌)
          (SimplicialCategory.homEquiv' _ _ f)))
          (PointedObject.basedHomMap (X.level n).space p).right ≫
            eComp SSet (W.level n).space (X.level n).space D := by
  rw [← Category.assoc, spectrumFixedLeftComposition_evaluation]
  simpa only [Category.assoc, Category.id_comp] using
    congrArg (OmegaSpectrum.evaluation X Z n ≫ ·)
      (pointedComposition_post
        (SSet.const ((OmegaSpectrum.evaluation W X n).app (Opposite.op ⦋0⦌)
          (SimplicialCategory.homEquiv' _ _ f))) (𝟙 _) p)

end SerrePositivity.KST.SConstruction
