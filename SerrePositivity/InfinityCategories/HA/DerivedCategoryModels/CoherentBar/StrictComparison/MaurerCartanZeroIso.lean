module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.MaurerCartanModuleMap
public import SerrePositivity.DifferentialGraded.Module.Graded

/-!
概要：零 MC 要素による微分変更は、元の全 dg 加群と同型である。
方針：全次数恒等写像を評価複体の同型として戻す。
規約：作用と全整数次数を保持する。
使われ方：bar の零段階と各段階の内部次元層。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory DifferentialGraded HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgBarModuleZero_maurerCartan (M : RightModule R D) :
    (moduleHom R D M M).d 1 2 0 + compose R (x := M) (y := M) (z := M)
      0 0 (show (1 : ℤ) + 1 = 2 from rfl) = 0 := by
  rw [map_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, zero_add]

def dgBarMaurerCartanZeroValueIso (M : RightModule R D) (x : Dᵒᵖ) :
    (moduleMaurerCartan R D M 0 (dgBarModuleZero_maurerCartan R D M)).obj x ≅ M.obj x :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun i j hij => by
    change i + 1 = j at hij
    subst j
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    erw [maurerCartanPerturbComplex_d]
    all_goals simp only [map_zero, δ_zero, Cochain.zero_comp, Cochain.zero_v, add_zero])

def dgBarMaurerCartanZeroIso (M : RightModule R D) :
    ForgetEnrichment.of (Complex R)
      (moduleMaurerCartan R D M 0 (dgBarModuleZero_maurerCartan R D M)) ≅
        ForgetEnrichment.of (Complex R) M :=
  moduleIsoMk R D (dgBarMaurerCartanZeroValueIso R D M) (fun x y => by
    apply HomologicalComplex.Hom.ext
    funext p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Cochain.ext
    intro i j hij
    simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply, homPostcompose_apply,
      homPrecompose_apply, Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
      Cochain.ofHom_v, dgBarMaurerCartanZeroValueIso,
      HomologicalComplex.Hom.isoOfComponents_hom_f, Iso.refl_hom,
      Category.id_comp, Category.comp_id]
    exact moduleMaurerCartanMap_v R D M 0 (dgBarModuleZero_maurerCartan R D M) x y p a i j hij)

@[simp]
lemma dgBarMaurerCartanZeroIso_hom_eval_f (M : RightModule R D) (x : D) (q : ℤ) :
    ((moduleEvaluation R D x).map (dgBarMaurerCartanZeroIso R D M).hom).f q = 𝟙 _ := by
  rw [dgBarMaurerCartanZeroIso, moduleIsoMk_hom_eval]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
