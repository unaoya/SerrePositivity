module
public import SerrePositivity.InfinityCategories.Derived.DGKernelResolutionPerfectComparison
public import SerrePositivity.InfinityCategories.Derived.DGPerfectModulesInfinity
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 同じ実分解の半自由出力による perfect 模型。 -/
def dgPerfectKernelModuleDG (P : Bimodule R E D) :
    DGFunctor R (PerfectDGModule R D) (RightModule R E) :=
  (perfectDGModuleInclusion R D Set.univ).comp (Morita.kernelTensor R D E P)
/-- 同じ実分解の半自由出力による perfect 模型。 -/
lemma dgPerfectKernelResolution_replacement_perfect
    (P : Bimodule R E D) [(Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence]
    (X : DGModuleFunctorResolutionObject R (PerfectDGModule R D) E
      (dgPerfectKernelModuleDG R D E P)) :
    modulePerfect R E ((moduleToDerived R E).obj
      (ForgetEnrichment.of (Complex R) X.replacement.val)) := by
  let K := Morita.kernelDerivedTensorOnBimodule R D E P
  have : (Morita.kernelDerivedTensor R D E
      ((bimoduleToDerived R E D).obj (BimoduleCategory.of R E D P))).Additive :=
    Morita.kernelBrownActionAdditive R D E _
  have : K.Additive := Functor.additive_of_iso
    (Morita.kernelDerivedTensorOnBimoduleIso R D E (BimoduleCategory.of R E D P))
  have : K.asEquivalence.functor.Additive := by change K.Additive; infer_instance
  have hx := (dgModulePerfect_equivalence_iff R D E K.asEquivalence _).mpr X.source.property.2
  let M := ForgetEnrichment.of (Complex R) X.source.val
  let Q := moduleIdentityProjectiveResolution R D M X.source.property.1
  have e := Morita.kernelDerivedTensorOnBimoduleComputation R D E P Q
  have hk := (modulePerfect R E).prop_of_iso e hx
  have hi : IsIso ((moduleToDerived R E).map X.augmentation) :=
    moduleToDerived_inverts R E X.augmentation X.quasiIso
  exact (modulePerfect R E).prop_of_iso (asIso ((moduleToDerived R E).map X.augmentation)).symm hk
/-- 同じ実分解の半自由出力による perfect 模型。 -/
def dgPerfectKernelResolutionReplacement
    (P : Bimodule R E D) [(Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence] :
    DGFunctor R (DGModuleFunctorResolutionObject R (PerfectDGModule R D) E
      (dgPerfectKernelModuleDG R D E P)) (PerfectDGModule R E) where
  obj X := ⟨X.replacement.val, dgSemifreeModule_isProjective R E X.replacement,
    dgPerfectKernelResolution_replacement_perfect R D E P X⟩
  map X Y := (dgModuleFunctorResolutionReplacement R (PerfectDGModule R D) E
    (dgPerfectKernelModuleDG R D E P)).map X Y
  map_id X := (dgModuleFunctorResolutionReplacement R (PerfectDGModule R D) E
    (dgPerfectKernelModuleDG R D E P)).map_id X
  map_comp X Y Z := (dgModuleFunctorResolutionReplacement R (PerfectDGModule R D) E
    (dgPerfectKernelModuleDG R D E P)).map_comp X Y Z
/-- 同じ実分解の半自由出力による perfect 模型。 -/
lemma dgPerfectKernelResolutionReplacement_projective
    (P : Bimodule R E D) [(Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence] :
    (dgPerfectKernelResolutionReplacement R D E P).comp (dgPerfectToProjective R E) =
    (dgModuleFunctorResolutionReplacement R (PerfectDGModule R D) E
      (dgPerfectKernelModuleDG R D E P)).comp (dgSemifreeToProjective R E) := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, dgPerfectToProjective, dgFullFunctorRestriction,
    dgPerfectKernelResolutionReplacement,
    Category.comp_id, eqToHom_refl]
end SerrePositivity.InfinityCategories
