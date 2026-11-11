module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ConeModuleMapLeftComparison
public import Mathlib.Algebra.Homology.QuasiIso

/-! 全 dg 自然な円錐射の評価は、構成済みの点ごとの実ホモトピー同値の順射そのもの。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
  (p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingConeRepresentative R C Y.left Z.left (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftArrow R C D M Y Z f))
  (q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingConeRepresentative R D Y.right Z.right
    ((dgYoneda R D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightArrow R C D M Y Z f)))

/-- 同じ両包含を持つ実鎖写像の一意性による、評価と既存同値の順射の一致。 -/
lemma dgGluingConeModuleMapEvaluation_eq :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeModuleMapEvaluation R C D M Y Z f p q X =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeNativeRepresentativeEquiv R C D M X Y Z f p q).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  apply mappingCone.ext_from (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M X Y Z f) (n + 1) n rfl
  · have h := Cochain.congr_v
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeModuleMapEvaluation_inl_comparison R C D M X Y Z f p q)
      (n + 1) n (by omega)
    simpa only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v] using h
  · have h := congrArg (fun a => a.f n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeModuleMapEvaluation_inr_comparison R C D M X Y Z f p q)
    simpa only [HomologicalComplex.comp_f] using h

/-- 全 dg 自然な同じ加群円錐射の native Hom 評価は準同型。 -/
lemma dgGluingConeModuleMapEvaluation_quasiIso :
    QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeModuleMapEvaluation R C D M Y Z f p q X) := by
  rw [dgGluingConeModuleMapEvaluation_eq]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeNativeRepresentativeEquiv R C D M X Y Z f p q).quasiIso_hom

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
