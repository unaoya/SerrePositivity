module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.FactorObjects
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.LeftFactorHom
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! C 因子の元の C との dg 準同値と、二充満因子の半直交 Hom の acyclic 性。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory HomologicalComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)

omit [Small.{u} D] in
/-- 同じ C 因子の射影は、すべての実 Hom 複体で quasi-isomorphism。 -/
lemma dgGluingCFactorProjection_homQuasiIso : HomQuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCFactorProjection R C D M) := by
  intro X Y
  change QuasiIso (𝟙 _ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X.val Y.val)
  rw [Category.id_comp]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap_quasiIso_of_target_right_zero R C D M X.val Y.val Y.property

lemma dgGluingCFactorProjection_essSurj (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCFactorProjection R C D M).onHomotopy.EssSurj where
  mem_essImage Y := by
    let c := ForgetEnrichment.to (Complex R) Y.as
    refine ⟨(toHomotopy R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingCFactor R C D M)).obj
      (ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCFactorObject R C D M c hD)), ⟨?_⟩⟩
    exact Iso.refl _

/-- 追加の零対象仮定なしに、実 C 因子と元の C の dg 準同値を供給。 -/
lemma dgGluingCFactorProjection_quasiEquivalence (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D) :
    QuasiEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCFactorProjection R C D M) :=
  ⟨dgGluingCFactorProjection_homQuasiIso R C D M,
    dgGluingCFactorProjection_essSurj R C D M hD⟩

omit [Small.{u} D] in
/-- 順序 ⟨D,C⟩ の二充満因子の間では、実 Hom 複体が全次数 acyclic。 -/
lemma dgGluingFactors_semiorthogonal
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingDFactor R C D M) (Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingCFactor R C D M) :
    (homObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) X.val Y.val).Acyclic :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHom_acyclic_D_to_C R C D M X.val Y.val X.property Y.property

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
