module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentCutGradedSplitting
public import SerrePositivity.DifferentialGraded.Module.Graded

/-!
概要：隣接する実 MC 段階と最高次元層は、全次数作用に関して分裂した拡大をなす。
方針：内部直和の分裂公式を同じ成分で戻し、全斉次作用の自然性を保持する。
規約：section と retraction の閉性は主張しない。
使われ方：h-projective 性の拡大閉性と Hom 制限の次数別全射性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
open HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

lemma dgBarModuleMorphism_action_naturality {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D} (f : M ⟶ N)
    (x y : D) (p i j : ℤ) (hij : i + p = j)
    (a : _root_.SerrePositivity.DifferentialGraded.GradedHom R (Opposite.op x) (Opposite.op y) p) :
    _root_.SerrePositivity.DifferentialGraded.moduleActionComponent R D M x y p i j hij a ≫ ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D y).map f).f j =
      ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map f).f i ≫ moduleActionComponent R D N x y p i j hij a := by
  have h := congrArg (fun g => (g.f p a).v i j hij)
    ((_root_.SerrePositivity.DifferentialGraded.moduleMapFamilyEquiv R D M N f).property (Opposite.op x) (Opposite.op y))
  simpa only [HomologicalComplex.comp_f, ModuleCat.comp_apply, _root_.SerrePositivity.DifferentialGraded.homPostcompose_apply,
    _root_.SerrePositivity.DifferentialGraded.homPrecompose_apply, Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v] using! h

variable {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

def dgCoherentBarCutGradedSplit (n : ℕ) :
    ModuleGradedSplit R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutModuleMap R D G (Nat.le_succ n))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutToLayer R D G (n + 1)) where
  retraction x q := ((moduleEvaluation R D x).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGradedRetraction R D G n)).f q
  section_ x q := ((moduleEvaluation R D x).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGradedSection R D G n)).f q
  inclusion_retraction x q := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutModuleMap_eval_f, ← HomologicalComplex.comp_f,
      ← CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGraded_inclusion_retraction,
      CategoryTheory.Functor.map_id, HomologicalComplex.id_f]
    rfl
  section_projection x q := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutToLayer_eval_f, ← HomologicalComplex.comp_f,
      ← CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGraded_section_projection,
      CategoryTheory.Functor.map_id, HomologicalComplex.id_f]
  section_retraction x q := by
    rw [← HomologicalComplex.comp_f, ← CategoryTheory.Functor.map_comp,
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGraded_section_retraction, CategoryTheory.Functor.map_zero,
      HomologicalComplex.zero_f]
  inclusion_projection := by
    apply _root_.SerrePositivity.DifferentialGraded.moduleMorphism_ext
    intro x
    apply HomologicalComplex.Hom.ext
    funext q
    simp only [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f,
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutModuleMap_eval_f, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutToLayer_eval_f,
      CategoryTheory.Functor.map_zero, HomologicalComplex.zero_f]
    rw [← HomologicalComplex.comp_f, ← CategoryTheory.Functor.map_comp,
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGraded_inclusion_projection, CategoryTheory.Functor.map_zero,
      HomologicalComplex.zero_f]
  decomposition x q := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutModuleMap_eval_f, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutToLayer_eval_f,
      ← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f,
      ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      ← HomologicalComplex.add_f_apply, ← CategoryTheory.Functor.map_add,
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGraded_decomposition, CategoryTheory.Functor.map_id,
      HomologicalComplex.id_f]
    rfl
  retraction_naturality x y p i j hij a := by
    change moduleActionComponent R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGraded R D G (n + 1)) x y p i j hij a ≫
      ((moduleEvaluation R D y).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGradedRetraction R D G n)).f j =
      ((moduleEvaluation R D x).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGradedRetraction R D G n)).f i ≫
        moduleActionComponent R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGraded R D G n) x y p i j hij a
    exact dgBarModuleMorphism_action_naturality R D _ x y p i j hij a
  section_naturality x y p i j hij a := by
    change ((moduleEvaluation R D x).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGradedSection R D G n)).f i ≫
      moduleActionComponent R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGraded R D G (n + 1)) x y p i j hij a =
      moduleActionComponent R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G (n + 1)) x y p i j hij a ≫
        ((moduleEvaluation R D y).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGradedSection R D G n)).f j
    exact (dgBarModuleMorphism_action_naturality R D _ x y p i j hij a).symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
