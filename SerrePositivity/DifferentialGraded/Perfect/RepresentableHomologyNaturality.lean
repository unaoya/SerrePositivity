module
public import SerrePositivity.DifferentialGraded.Perfect.RepresentableHomologyLinear
public import SerrePositivity.DifferentialGraded.Category.HomotopyHomologyNaturality
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveDerivedLifting
public import SerrePositivity.DifferentialGraded.Module.HomCycles

/-! # 代表加群の導来Hom計算と後合成の自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleProjectiveDerivedHomologyEquiv_postcompose {P M N : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P)
    (f : (moduleToDerived A D).obj P ⟶ (moduleToDerived A D).obj M) (g : M ⟶ N) :
    moduleProjectiveDerivedHomologyEquiv A D hP N (f ≫ (moduleToDerived A D).map g) =
      homologyMap (eHomWhiskerLeft (Complex A) P g) 0
        (moduleProjectiveDerivedHomologyEquiv A D hP M f) := by
  obtain ⟨f, rfl⟩ := moduleProjectiveToDerived_map_surjective A D hP f
  rw [← (moduleToDerived A D).map_comp, moduleProjectiveDerivedHomologyEquiv_map,
    moduleProjectiveDerivedHomologyEquiv_map, complexZeroHomologyClass_naturality,
    closedHomEquiv_postcompose]

lemma dgYonedaIso_postcompose (x : D) {M N : ModuleCategory A D} (f : M ⟶ N) :
    eHomWhiskerLeft (Complex A)
        (ForgetEnrichment.of (Complex A) (representable A x) : ModuleCategory A D) f ≫
      (dgYonedaIso A x (ForgetEnrichment.to (Complex A) N)).hom =
    (dgYonedaIso A x (ForgetEnrichment.to (Complex A) M)).hom ≫
      (moduleEvaluation A D x).map f := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (yonedaEvaluateFamily A x (ForgetEnrichment.to (Complex A) N)
    (fun y => moduleHomπ A D (representable A x) (ForgetEnrichment.to (Complex A) N) y.unop)).f q
      ((eHomWhiskerLeft (Complex A)
        (ForgetEnrichment.of (Complex A) (representable A x) : ModuleCategory A D) f).f q z) =
    ((moduleEvaluation A D x).map f).f q
      ((yonedaEvaluateFamily A x (ForgetEnrichment.to (Complex A) M)
        (fun y => moduleHomπ A D (representable A x) (ForgetEnrichment.to (Complex A) M)
          y.unop)).f q z)
  rw [yonedaEvaluateFamily_apply, yonedaEvaluateFamily_apply]
  have hp : (moduleHomπ A D (representable A x) (ForgetEnrichment.to (Complex A) N) x).f q
      ((eHomWhiskerLeft (Complex A)
        (ForgetEnrichment.of (Complex A) (representable A x) : ModuleCategory A D) f).f q z) =
      ((moduleHomπ A D (representable A x) (ForgetEnrichment.to (Complex A) M) x).f q z).comp
        (Cochain.ofHom ((moduleEvaluation A D x).map f)) (add_zero q) :=
    moduleHomWhiskerLeft_apply_π A D f q z x
  have hv := congrArg (fun k : Cochain ((representable A x).obj (op x))
      ((ForgetEnrichment.to (Complex A) N).obj (op x)) q =>
    k.v 0 q (by omega) (unitElement A x).val) hp
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, ModuleCat.comp_apply] at hv
  exact hv

lemma moduleRepresentableDerivedHomologyEquiv_postcompose (x : D) {M N : ModuleCategory A D}
    (f : (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶
      (moduleToDerived A D).obj M) (g : M ⟶ N) :
    moduleRepresentableDerivedHomologyEquiv A D x N (f ≫ (moduleToDerived A D).map g) =
      homologyMap ((moduleEvaluation A D x).map g) 0
        (moduleRepresentableDerivedHomologyEquiv A D x M f) := by
  change homologyMap (dgYonedaIso A x (ForgetEnrichment.to (Complex A) N)).hom 0
    (moduleProjectiveDerivedHomologyEquiv A D
      (representable_homotopicallyProjective A D x) N (f ≫ (moduleToDerived A D).map g)) = _
  rw [moduleProjectiveDerivedHomologyEquiv_postcompose]
  have h := congrArg (fun k => homologyMap k 0) (dgYonedaIso_postcompose A D x g)
  simp only [homologyMap_comp] at h
  exact congrArg (fun k => k
    (moduleProjectiveDerivedHomologyEquiv A D (representable_homotopicallyProjective A D x) M f)) h

end SerrePositivity.DifferentialGraded
