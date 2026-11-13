module
public import SerrePositivity.KST.SConstruction.PerfectInvariantZeroMap
public import SerrePositivity.KST.SConstruction.TammePerfectValueSplit

/-! # 元の lax 両射影の値と両包含上の作用
概要：元の二射影を実 BF 積への一つの射の類へ束ね、両軸への作用を回収する。
方針：同じ完全関手の合成則・零関手の像の零性を、実積の外延性へ渡す。
規約：同じ元の二射影を使う。使われ方：Tamme の射影を保つ積同値。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet Spectra
open SerrePositivity.InfinityCategories LocalizingInvariants

open scoped Simplicial
variable {C D B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D B)
  (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete C.obj) (hD : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete D.obj)
  (F : perfectStableInfinity.{u} ⟶ Sp.{u})

/-- 元の両射影の値を持つ、元の C・D の値の実積への射の類。 -/
def tammePerfectProjectionHom :
    SpectrumHo.obj (perfectInvariantSpectrum F (perfectLaxVertex p q hC hD)) ⟶
    SpectrumHo.obj (Binary.obj
      (perfectInvariantSpectrum F (perfectStableVertex C hC))
      (perfectInvariantSpectrum F (perfectStableVertex D hD))) :=
  Binary.hoLift
    (perfectInvariantSpectrumHom F (laxFst p q)
      (perfectLaxCategory_isIdempotentComplete p q hC hD) hC)
    (perfectInvariantSpectrumHom F (laxSnd p q)
      (perfectLaxCategory_isIdempotentComplete p q hC hD) hD)

/-- 実積の第一射影は、元の同じ lax 第一射影の値を回収する。 -/
lemma tammePerfectProjectionHom_fst : tammePerfectProjectionHom p q hC hD F ≫
    SpectrumHo.hom (Binary.fst
      (perfectInvariantSpectrum F (perfectStableVertex C hC))
      (perfectInvariantSpectrum F (perfectStableVertex D hD))) =
    perfectInvariantSpectrumHom F (laxFst p q)
      (perfectLaxCategory_isIdempotentComplete p q hC hD) hC := Binary.hoLift_fst _ _

/-- 実積の第二射影は、元の同じ lax 第二射影の値を回収する。 -/
lemma tammePerfectProjectionHom_snd : tammePerfectProjectionHom p q hC hD F ≫
    SpectrumHo.hom (Binary.snd
      (perfectInvariantSpectrum F (perfectStableVertex C hC))
      (perfectInvariantSpectrum F (perfectStableVertex D hD))) =
    perfectInvariantSpectrumHom F (laxSnd p q)
      (perfectLaxCategory_isIdempotentComplete p q hC hD) hD := Binary.hoLift_snd _ _

variable {F} (hF : IsPerfectLocalizingInvariant F)

include hF in
/-- 元の C 包含の値を合成すると、実積の C 軸そのものになる。 -/
lemma IsPerfectLocalizingInvariant.tammePerfectProjectionHom_fromC :
    perfectInvariantSpectrumHom F (LaxInclusion.exactFromC p q) hC
        (perfectLaxCategory_isIdempotentComplete p q hC hD) ≫
      tammePerfectProjectionHom p q hC hD F =
    SpectrumHo.hom (Binary.inl
      (perfectInvariantSpectrum F (perfectStableVertex C hC))
      (perfectInvariantSpectrum F (perfectStableVertex D hD))) := by
  have hc : perfectInvariantSpectrumHom F (LaxInclusion.exactFromC p q) hC
      (perfectLaxCategory_isIdempotentComplete p q hC hD) ≫
      perfectInvariantSpectrumHom F (laxFst p q)
        (perfectLaxCategory_isIdempotentComplete p q hC hD) hC = 𝟙 _ := by
    rw [← perfectInvariantSpectrumHom_comp]
    have he : (LaxInclusion.exactFromC p q : C ⟶ laxCategory p q) ≫ laxFst p q = 𝟙 C :=
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext (LaxInclusion.fromC_fst p q)
    rw [he, perfectInvariantSpectrumHom_id]
  have hd : perfectInvariantSpectrumHom F (LaxInclusion.exactFromC p q) hC
      (perfectLaxCategory_isIdempotentComplete p q hC hD) ≫
      perfectInvariantSpectrumHom F (laxSnd p q)
        (perfectLaxCategory_isIdempotentComplete p q hC hD) hD = 0 := by
    let f : C ⟶ D := (LaxInclusion.exactFromC p q : C ⟶ laxCategory p q) ≫ laxSnd p q
    have hz := hF.perfectSpectrum_zero_of_zero_values f hC hD (by
      intro c
      change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((LaxInclusion.fromC p q ≫ (laxSnd p q).hom).app _ c)
      rw [LaxInclusion.fromC_snd, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.zeroD, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagram_const_vertex]
      exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex D.obj).isZero)
    change perfectInvariantSpectrumHom F
      (show C ⟶ D from (LaxInclusion.exactFromC p q : C ⟶ laxCategory p q) ≫ laxSnd p q)
      hC hD = 0 at hz
    rw [perfectInvariantSpectrumHom_comp] at hz
    exact hz
  apply Binary.ho_hom_ext
  · erw [Category.assoc, tammePerfectProjectionHom_fst, hc, Binary.ho_inl_fst]
  · erw [Category.assoc, tammePerfectProjectionHom_snd, hd, Binary.ho_inl_snd]

include hF in
/-- 元の D 包含の値を合成すると、実積の D 軸そのものになる。 -/
lemma IsPerfectLocalizingInvariant.tammePerfectProjectionHom_fromD :
    perfectInvariantSpectrumHom F (LaxInclusion.exactFromD p q) hD
        (perfectLaxCategory_isIdempotentComplete p q hC hD) ≫
      tammePerfectProjectionHom p q hC hD F =
    SpectrumHo.hom (Binary.inr
      (perfectInvariantSpectrum F (perfectStableVertex C hC))
      (perfectInvariantSpectrum F (perfectStableVertex D hD))) := by
  have hc : perfectInvariantSpectrumHom F (LaxInclusion.exactFromD p q) hD
      (perfectLaxCategory_isIdempotentComplete p q hC hD) ≫
      perfectInvariantSpectrumHom F (laxFst p q)
        (perfectLaxCategory_isIdempotentComplete p q hC hD) hC = 0 := by
    let f : D ⟶ C := (LaxInclusion.exactFromD p q : D ⟶ laxCategory p q) ≫ laxFst p q
    have hz := hF.perfectSpectrum_zero_of_zero_values f hD hC (by
      intro d
      change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((LaxInclusion.fromD p q ≫ (laxFst p q).hom).app _ d)
      rw [LaxInclusion.fromD_fst, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.zeroC, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagram_const_vertex]
      exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex C.obj).isZero)
    change perfectInvariantSpectrumHom F
      (show D ⟶ C from (LaxInclusion.exactFromD p q : D ⟶ laxCategory p q) ≫ laxFst p q)
      hD hC = 0 at hz
    rw [perfectInvariantSpectrumHom_comp] at hz
    exact hz
  have hd : perfectInvariantSpectrumHom F (LaxInclusion.exactFromD p q) hD
      (perfectLaxCategory_isIdempotentComplete p q hC hD) ≫
      perfectInvariantSpectrumHom F (laxSnd p q)
        (perfectLaxCategory_isIdempotentComplete p q hC hD) hD = 𝟙 _ := by
    rw [← perfectInvariantSpectrumHom_comp]
    have he : (LaxInclusion.exactFromD p q : D ⟶ laxCategory p q) ≫ laxSnd p q = 𝟙 D :=
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext (LaxInclusion.fromD_snd p q)
    rw [he, perfectInvariantSpectrumHom_id]
  apply Binary.ho_hom_ext
  · erw [Category.assoc, tammePerfectProjectionHom_fst, hc, Binary.ho_inr_fst]
  · erw [Category.assoc, tammePerfectProjectionHom_snd, hd, Binary.ho_inr_snd]

end SerrePositivity.KST.SConstruction
