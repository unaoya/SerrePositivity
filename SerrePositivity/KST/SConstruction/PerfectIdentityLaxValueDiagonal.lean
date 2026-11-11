module
public import SerrePositivity.KST.SConstruction.TammePerfectProjectionEquivalence
public import SerrePositivity.KST.LocalizingInvariants.IdentityLaxDiagonal

/-! # 恒等 lax 対角の同じ値と元の実 BF 積の対角
概要：元の恒等 lax 対角の値は、元の両射影同値の下で実積の対角となる。
方針：元の二つの厳密射影式を同じ BF 表示の射の類へ写し、積の外延性を使う。
規約：元の完全関手と実 BF 積を保持する。使われ方：移送した正方形の上辺。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories LocalizingInvariants

variable (F : perfectStableInfinity.{u} ⟶ Sp.{u})
  (Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) (hQ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete Q.obj)

/-- 恒等 lax 対角の値の第一射影は、元の同じ値の恒等射。 -/
lemma perfectIdentityLaxValueDiagonal_fst :
    perfectInvariantSpectrumHom F (IdentityLax.exactDiagonal Q) hQ
        (perfectLaxCategory_isIdempotentComplete (𝟙 Q) (𝟙 Q) hQ hQ) ≫
      perfectInvariantSpectrumHom F (laxFst (𝟙 Q) (𝟙 Q))
        (perfectLaxCategory_isIdempotentComplete (𝟙 Q) (𝟙 Q) hQ hQ) hQ = 𝟙 _ := by
  have he : (IdentityLax.exactDiagonal Q : Q ⟶ laxCategory (𝟙 Q) (𝟙 Q)) ≫
      laxFst (𝟙 Q) (𝟙 Q) = 𝟙 Q := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext (IdentityLax.diagonal_fst Q)
  rw [← perfectInvariantSpectrumHom_comp, he, perfectInvariantSpectrumHom_id]

/-- 恒等 lax 対角の値の第二射影は、元の同じ値の恒等射。 -/
lemma perfectIdentityLaxValueDiagonal_snd :
    perfectInvariantSpectrumHom F (IdentityLax.exactDiagonal Q) hQ
        (perfectLaxCategory_isIdempotentComplete (𝟙 Q) (𝟙 Q) hQ hQ) ≫
      perfectInvariantSpectrumHom F (laxSnd (𝟙 Q) (𝟙 Q))
        (perfectLaxCategory_isIdempotentComplete (𝟙 Q) (𝟙 Q) hQ hQ) hQ = 𝟙 _ := by
  have he : (IdentityLax.exactDiagonal Q : Q ⟶ laxCategory (𝟙 Q) (𝟙 Q)) ≫
      laxSnd (𝟙 Q) (𝟙 Q) = 𝟙 Q := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext (IdentityLax.diagonal_snd Q)
  rw [← perfectInvariantSpectrumHom_comp, he, perfectInvariantSpectrumHom_id]

variable {F} (hF : IsPerfectLocalizingInvariant F)

/-- 元の対角の値は、元の両射影同値の下で実 BF 積の同じ対角になる。 -/
lemma IsPerfectLocalizingInvariant.perfectIdentityLaxValueDiagonal_product :
    perfectInvariantSpectrumHom F (IdentityLax.exactDiagonal Q) hQ
        (perfectLaxCategory_isIdempotentComplete (𝟙 Q) (𝟙 Q) hQ hQ) ≫
      (hF.tammePerfectProjectionEquivalence (𝟙 Q) (𝟙 Q) hQ hQ).hom =
    SpectrumHo.hom (Binary.lift
      (𝟙 (perfectInvariantSpectrum F (perfectStableVertex Q hQ)))
      (𝟙 (perfectInvariantSpectrum F (perfectStableVertex Q hQ)))) := by
  apply Binary.ho_hom_ext
  · erw [Category.assoc, hF.tammePerfectProjectionEquivalence_fst,
      perfectIdentityLaxValueDiagonal_fst, ← SpectrumHo.hom_comp,
      Binary.lift_fst, SpectrumHo.hom_id]
  · erw [Category.assoc, hF.tammePerfectProjectionEquivalence_snd,
      perfectIdentityLaxValueDiagonal_snd, ← SpectrumHo.hom_comp,
      Binary.lift_snd, SpectrumHo.hom_id]

end SerrePositivity.KST.SConstruction
