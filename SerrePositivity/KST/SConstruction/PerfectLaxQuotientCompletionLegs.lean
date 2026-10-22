module
public import SerrePositivity.KST.SConstruction.PerfectLaxQuotientComparison
public import SerrePositivity.KST.SConstruction.PerfectInvariantSpectrum
public import SerrePositivity.KST.LocalizingInvariants.SuspensionExactNaturality

/-! # 元の商の二脚と完備化後の商射から作る二脚の比較
概要：元の商の C・D 二脚の完備化像を、完備化後の商射の二脚へ照合する。
方針：C 側は完全関手の suspension 自然性と元の shift 比較を使い、D 側は合成則。
規約：逆 shift と完備化を厳密可換とは仮定しない。使われ方：LT の元の二脚の回収。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories LocalizingInvariants
namespace PerfectLaxQuotient
variable {C D B : StableCategory.{u}} {p : ExactMap C B} {q : ExactMap D B}
  (d : PerfectLaxQuotient p q)

/-- 元の C 脚の完備化像は、完備化後の商射から作る C 脚と全関手同型。 -/
def cLeg_projectionIso : FunctorIso d.cLeg.hom
    (laxQuotientCLeg p q d.sequence.projection).hom := by
  let r : ExactMap (laxCategory p q) d.right := d.sequence.projection
  change FunctorIso d.cLeg.hom (laxQuotientCLeg p q r).hom
  apply ((SuspensionExact.equivalence d.right.obj).isQCatEquivalence.postcompose
    C.obj).isFullyFaithful.preimageVertexIso
  have en := FunctorIso.precomp
    (SuspensionExact.exactNaturality d.completion.hom).symm
    (laxQuotientCLeg p q d.rawProjection).hom
  have er := FunctorIso.postcomp
    (laxQuotientCLeg_suspensionIso p q d.rawProjection) d.completion.hom
  have ec := laxQuotientCLeg_suspensionIso p q r
  have en' : FunctorIso
      (d.cLeg.hom ≫ SuspensionExact.map d.right.obj)
      (((laxQuotientCLeg p q d.rawProjection).hom ≫
        SuspensionExact.map d.rawQuotient.obj) ≫ d.completion.hom) := by
    simpa only [cLeg, Category.assoc] using en
  have ec' : FunctorIso
      ((LaxInclusion.fromC p q ≫ d.rawProjection.hom) ≫ d.completion.hom)
      ((laxQuotientCLeg p q r).hom ≫ SuspensionExact.map d.right.obj) := by
    have he : (LaxInclusion.fromC p q ≫ d.rawProjection.hom) ≫ d.completion.hom =
        LaxInclusion.fromC p q ≫ r.hom := Category.assoc _ _ _
    rw [he]
    exact ec.symm
  exact en' ≪≫ er ≪≫ ec'

/-- 元の D 脚の完備化像は、完備化後の商射から作る同じ D 脚。 -/
lemma dLeg_projection_eq : d.dLeg = laxQuotientDLeg p q d.sequence.projection := by
  apply ExactMap.ext
  exact Category.assoc _ _ _

/-- C 側の全関手同型は、同じ BF 表示間の値の射の類を等しくする。 -/
lemma cLeg_projection_value (F : perfectStableInfinity.{u} ⟶ Sp.{u}) :
    perfectInvariantSpectrumHom F d.cLeg d.c_complete d.right_complete =
      perfectInvariantSpectrumHom F (laxQuotientCLeg p q d.sequence.projection)
        d.c_complete d.sequence.right_complete := by
  exact congrArg SpectrumHo.normalize
    (perfectInvariantHoArrow_eq_of_functorIso F d.c_complete d.right_complete d.cLeg_projectionIso)

/-- D 側の厳密な回収も、同じ BF 表示間の値の射の類を保つ。 -/
lemma dLeg_projection_value (F : perfectStableInfinity.{u} ⟶ Sp.{u}) :
    perfectInvariantSpectrumHom F d.dLeg d.d_complete d.right_complete =
      perfectInvariantSpectrumHom F (laxQuotientDLeg p q d.sequence.projection)
        d.d_complete d.sequence.right_complete := by
  rw [d.dLeg_projection_eq]
  rfl

end PerfectLaxQuotient
end SerrePositivity.KST.SConstruction
