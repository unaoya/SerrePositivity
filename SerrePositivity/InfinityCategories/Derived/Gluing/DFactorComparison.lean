module
public import SerrePositivity.InfinityCategories.Derived.Gluing.FactorObjects
public import SerrePositivity.InfinityCategories.Derived.Gluing.RightFactorHom
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! D 因子の右射影は、元の D との実 dg 準同値。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory HomologicalComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

/-- 同じ D 因子の射影は、すべての実 Hom 複体で quasi-isomorphism。 -/
lemma dgGluingDFactorProjection_homQuasiIso : HomQuasiIso (dgGluingDFactorProjection R C D M) := by
  intro X Y
  change QuasiIso (𝟙 _ ≫ (dgGluingRight R C D M).map X.val Y.val)
  rw [Category.id_comp, dgGluingRight_map]
  exact dgGluingRightHomMap_quasiIso_of_source_left_zero R C D M X.val Y.val X.property

lemma dgGluingDFactorProjection_essSurj (hC : IsDGPretriangulated R C) :
    (dgGluingDFactorProjection R C D M).onHomotopy.EssSurj where
  mem_essImage Y := by
    let c := ForgetEnrichment.to (Complex R) Y.as
    refine ⟨(toHomotopy R (DGGluingDFactor R C D M)).obj
      (ForgetEnrichment.of (Complex R) (dgGluingDFactorObject R C D M c hC)), ⟨?_⟩⟩
    exact Iso.refl _

/-- 追加の零対象仮定なしに、実 D 因子と元の D の dg 準同値を供給。 -/
lemma dgGluingDFactorProjection_quasiEquivalence (hC : IsDGPretriangulated R C) :
    QuasiEquivalence (dgGluingDFactorProjection R C D M) :=
  ⟨dgGluingDFactorProjection_homQuasiIso R C D M,
    dgGluingDFactorProjection_essSurj R C D M hC⟩

end SerrePositivity.InfinityCategories
