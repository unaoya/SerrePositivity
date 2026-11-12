module
public import SerrePositivity.DifferentialGraded.Module.Basic
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison

/-! 元の全 Yoneda 鎖同型は、任意の閉加群射による後合成と厳密に可換。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]

lemma dgGluingYonedaIso_postcompose (c : C) {N P : RightModule R C}
    (f : ForgetEnrichment.of (Complex R) N ⟶ ForgetEnrichment.of (Complex R) P) :
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (representable R c)) f ≫
      (dgYonedaIso R c P).hom =
    (dgYonedaIso R c N).hom ≫ (moduleEvaluation R C c).map f := by
  apply HomologicalComplex.hom_ext
  intro k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (dgYonedaIso R c P).hom.f k
      ((eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) (representable R c)) f).f k z) =
    ((moduleEvaluation R C c).map f).f k ((dgYonedaIso R c N).hom.f k z)
  dsimp only [dgYonedaIso]
  rw [yonedaEvaluateFamily_apply, yonedaEvaluateFamily_apply]
  erw [moduleHomWhiskerLeft_apply_π R C
    (T := ForgetEnrichment.of (Complex R) (representable R c)) f k z c]
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rfl

lemma dgGluingYonedaIso_inv_postcompose (c : C) {N P : RightModule R C}
    (f : ForgetEnrichment.of (Complex R) N ⟶ ForgetEnrichment.of (Complex R) P) :
    (dgYonedaIso R c N).inv ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (representable R c)) f =
    (moduleEvaluation R C c).map f ≫ (dgYonedaIso R c P).inv := by
  apply (cancel_mono (dgYonedaIso R c P).hom).mp
  rw [Category.assoc, dgGluingYonedaIso_postcompose, Iso.inv_hom_id_assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
