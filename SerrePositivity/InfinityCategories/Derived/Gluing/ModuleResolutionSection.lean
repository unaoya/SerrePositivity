module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedPrecomposition
public import SerrePositivity.InfinityCategories.Derived.DGModuleOutputResolutionValue
public import SerrePositivity.InfinityCategories.Derived.DGFunctorPinchedMap

/-! β5 の同じ実入力切断と実半自由射影を、元の導来比較そのものへ接続する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))

def dgGluingModuleResolutionSection : dgNerve R C ⟶
    dgNerve R (DGModuleFunctorResolutionObject R C E F) :=
  dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C) ≫
    (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv

lemma dgGluingModuleResolutionSection_vertex (x : C) :
    (dgGluingModuleResolutionSection R C E F).app (Opposite.op ⦋0⦌) (Simplex.vertex x) =
      Simplex.vertex (dgModuleOutputResolutionObject R C E F x) := by
  change (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv.app (Opposite.op ⦋0⦌)
    ((dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)).app
      (Opposite.op ⦋0⦌) (Simplex.vertex x)) = _
  rw [dgFunctorNerve_vertex]
  exact ((Simplex.vertexEquiv (A := R)
    (D := DGModuleFunctorResolutionObject R C E F)).symm_apply_apply _).symm

lemma dgGluingModuleResolutionSection_isQCatEquivalence :
    IsQCatEquivalence (dgGluingModuleResolutionSection R C E F) := by
  let e : dgNerve R C ≅
      dgNerve R (DGUniverseLift.{max (u + 1) v, max (u + 1) v} C) := {
    hom := dgNerve.map (dgUniverseLiftUp R C)
    inv := dgNerve.map (dgUniverseLiftDown R C)
    hom_inv_id := by rw [← dgNerve.map_comp, dgUniverseLiftUp_comp_down, dgNerve.map_id]
    inv_hom_id := by rw [← dgNerve.map_comp, dgUniverseLiftDown_comp_up, dgNerve.map_id] }
  exact (qCatEquivalenceOfIso e).isQCatEquivalence.comp
    (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).symm.isQCatEquivalence

lemma dgGluingModuleResolutionSection_replacement :
    dgGluingModuleResolutionSection R C E F ≫
      dgNerve.map (dgModuleFunctorResolutionReplacement R C E F) =
        dgModuleResolvedInfinity R C E F := by
  simpa only [dgGluingModuleResolutionSection, Category.assoc] using
    (dgModuleResolvedInfinity_eq_section_replacement R C E F).symm

end SerrePositivity.InfinityCategories
