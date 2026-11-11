module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelResolutionPerfectComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPerfectModulesInfinity
/-!
概要：perfect 入力の実分解の同じ半自由出力を、projective perfect 加群へ戻す。
方針：主導来作用の同値と恒等入力分解で perfect 性を示し、元の全 Hom 射影を保つ。
規約：生の kernel 出力の射影性は仮定しない。使われ方：一般 Morita の Perf 作用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 同じ実分解の半自由出力による perfect 模型。 -/
def dgPerfectKernelModuleDG (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    _root_.SerrePositivity.DifferentialGraded.DGFunctor R (_root_.SerrePositivity.DifferentialGraded.PerfectDGModule R D) (_root_.SerrePositivity.DifferentialGraded.RightModule R E) :=
  (_root_.SerrePositivity.DifferentialGraded.perfectDGModuleInclusion R D Set.univ).comp (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D E P)
/-- 同じ実分解の半自由出力による perfect 模型。 -/
lemma dgPerfectKernelResolution_replacement_perfect
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) [(_root_.SerrePositivity.DifferentialGraded.Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence]
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R (PerfectDGModule R D) E
      (dgPerfectKernelModuleDG R D E P)) :
    _root_.SerrePositivity.DifferentialGraded.modulePerfect R E ((_root_.SerrePositivity.DifferentialGraded.moduleToDerived R E).obj
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) X.replacement.val)) := by
  let K := _root_.SerrePositivity.DifferentialGraded.Morita.kernelDerivedTensorOnBimodule R D E P
  have : (_root_.SerrePositivity.DifferentialGraded.Morita.kernelDerivedTensor R D E
      ((_root_.SerrePositivity.DifferentialGraded.bimoduleToDerived R E D).obj (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E D P))).Additive :=
    _root_.SerrePositivity.DifferentialGraded.Morita.kernelBrownActionAdditive R D E _
  have : K.Additive := Functor.additive_of_iso
    (_root_.SerrePositivity.DifferentialGraded.Morita.kernelDerivedTensorOnBimoduleIso R D E (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E D P))
  have : K.asEquivalence.functor.Additive := by change K.Additive; infer_instance
  have hx := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfect_equivalence_iff R D E K.asEquivalence _).mpr X.source.property.2
  let M := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) X.source.val
  let Q := _root_.SerrePositivity.DifferentialGraded.moduleIdentityProjectiveResolution R D M X.source.property.1
  have e := _root_.SerrePositivity.DifferentialGraded.Morita.kernelDerivedTensorOnBimoduleComputation R D E P Q
  have hk := (_root_.SerrePositivity.DifferentialGraded.modulePerfect R E).prop_of_iso e hx
  have hi : IsIso ((_root_.SerrePositivity.DifferentialGraded.moduleToDerived R E).map X.augmentation) :=
    _root_.SerrePositivity.DifferentialGraded.moduleToDerived_inverts R E X.augmentation X.quasiIso
  exact (_root_.SerrePositivity.DifferentialGraded.modulePerfect R E).prop_of_iso (asIso ((_root_.SerrePositivity.DifferentialGraded.moduleToDerived R E).map X.augmentation)).symm hk
/-- 同じ実分解の半自由出力による perfect 模型。 -/
def dgPerfectKernelResolutionReplacement
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) [(_root_.SerrePositivity.DifferentialGraded.Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence] :
    DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R (PerfectDGModule R D) E
      (dgPerfectKernelModuleDG R D E P)) (_root_.SerrePositivity.DifferentialGraded.PerfectDGModule R E) where
  obj X := ⟨X.replacement.val, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModule_isProjective R E X.replacement,
    dgPerfectKernelResolution_replacement_perfect R D E P X⟩
  map X Y := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R (PerfectDGModule R D) E
    (dgPerfectKernelModuleDG R D E P)).map X Y
  map_id X := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R (PerfectDGModule R D) E
    (dgPerfectKernelModuleDG R D E P)).map_id X
  map_comp X Y Z := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R (PerfectDGModule R D) E
    (dgPerfectKernelModuleDG R D E P)).map_comp X Y Z
/-- 同じ実分解の半自由出力による perfect 模型。 -/
lemma dgPerfectKernelResolutionReplacement_projective
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) [(_root_.SerrePositivity.DifferentialGraded.Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence] :
    (dgPerfectKernelResolutionReplacement R D E P).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectToProjective R E) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R (PerfectDGModule R D) E
      (dgPerfectKernelModuleDG R D E P)).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjective R E) := by
  apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectToProjective, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullFunctorRestriction,
    dgPerfectKernelResolutionReplacement,
    Category.comp_id, eqToHom_refl]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
