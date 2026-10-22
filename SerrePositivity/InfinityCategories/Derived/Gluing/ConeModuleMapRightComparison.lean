module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ConeModuleMapEvaluation
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomConeNativeRepresentation

/-! 実加群円錐射と既存の点ごとの native Hom 同値の順射は、同じ右包含上で一致する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory CochainComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
  (p : DGGluingConeRepresentative R C Y.left Z.left (dgGluingConeLeftArrow R C D M Y Z f))
  (q : DGGluingConeRepresentative R D Y.right Z.right
    ((dgYoneda R D).onClosed.map (dgGluingConeRightArrow R C D M Y Z f)))
local notation "W" => dgGluingConeObjectFromRepresentatives R C D M Y Z f p q

/-- 既存の点ごとの Hom 同値の順射も、同じ native 円錐包含を右成分に持つ。 -/
lemma dgGluingHomConeNativeRepresentativeEquiv_inr :
    mappingCone.inr (dgGluingPostcomposition R C D M X Y Z f) ≫
      (dgGluingHomConeNativeRepresentativeEquiv R C D M X Y Z f p q).hom =
    dgGluingPostcomposition R C D M X Z W (dgGluingConeInr R C D M Y Z f p q) := by
  apply (cancel_mono (dgGluingKernelHomIso R C D M X W).hom).1
  rw [dgGluingHomConeNativeRepresentativeEquiv_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, dgGluingHomConeKernelIso_inr, Category.assoc]
  exact (dgGluingConeInrModuleMap_kernel R C D M Y Z f p q X).symm

/-- 全 dg 自然な加群射の評価と既存の点ごとの順射は、右包含への制限が厳密に同じ。 -/
lemma dgGluingConeModuleMapEvaluation_inr_comparison :
    mappingCone.inr (dgGluingPostcomposition R C D M X Y Z f) ≫
      dgGluingConeModuleMapEvaluation R C D M Y Z f p q X =
    mappingCone.inr (dgGluingPostcomposition R C D M X Y Z f) ≫
      (dgGluingHomConeNativeRepresentativeEquiv R C D M X Y Z f p q).hom := by
  rw [dgGluingConeModuleMap_eval_inr, dgGluingHomConeNativeRepresentativeEquiv_inr]

end SerrePositivity.InfinityCategories
