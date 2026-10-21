module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedPrecomposition
public import SerrePositivity.InfinityCategories.Derived.DGPerfectKernelResolution
/-!
概要：半自由入力と perfect 入力の kernel 作用を、同じ全射影的入力の作用へ比較する。
方針：実 dg 包含の合成等式と全関手的な出力分解の前合成比較を使う。
規約：元の全単体作用を保つ。使われ方：一般 kernel の Perf 包含四角形。
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
/-- 同じ全射影的入力への kernel 作用の比較。 -/
def dgProjectiveKernelModuleDG (P : Bimodule R E D) :
    DGFunctor R (ProjectiveDGModules R D) (RightModule R E) :=
  (dgFullSubcategoryInclusion R (RightModule R D) (dgModuleProjectiveProperty R D)).comp
    (Morita.kernelTensor R D E P)
/-- 同じ全射影的入力への kernel 作用の比較。 -/
lemma dgProjectiveKernelModuleDG_semifree (P : Bimodule R E D) :
    (dgSemifreeToProjective R D).comp (dgProjectiveKernelModuleDG R D E P) =
      dgSemifreeKernelModuleDG R D E P := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, dgSemifreeToProjective, dgProjectiveKernelModuleDG,
    dgFullSubcategoryInclusion, Category.id_comp, Category.comp_id, eqToHom_refl]
/-- 同じ全射影的入力への kernel 作用の比較。 -/
lemma dgProjectiveKernelModuleDG_perfect (P : Bimodule R E D) :
    (dgPerfectToProjective R D).comp (dgProjectiveKernelModuleDG R D E P) =
      dgPerfectKernelModuleDG R D E P := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, dgPerfectToProjective, dgFullFunctorRestriction,
    dgProjectiveKernelModuleDG, dgFullSubcategoryInclusion,
    Category.id_comp, Category.comp_id, eqToHom_refl]
/-- 同じ全射影的入力への kernel 作用の比較。 -/
def dgKernelDerivedInfinity_projectiveInputIso (P : Bimodule R E D) :
    FunctorIso (dgKernelDerivedInfinity R D E P)
      (dgNerve.map (dgSemifreeToProjective R D) ≫
        dgModuleResolvedInfinity R (ProjectiveDGModules R D) E
          (dgProjectiveKernelModuleDG R D E P)) := by
  have e := dgModuleResolvedInfinity_precompIso R (SemifreeDGModules R D)
    (ProjectiveDGModules R D) E (dgSemifreeToProjective R D) (dgProjectiveKernelModuleDG R D E P)
  rw [dgProjectiveKernelModuleDG_semifree] at e
  exact e
/-- 同じ全射影的入力への kernel 作用の比較。 -/
def dgPerfectKernelResolvedInfinity_projectiveInputIso (P : Bimodule R E D) :
    FunctorIso (dgModuleResolvedInfinity R (PerfectDGModule R D) E
      (dgPerfectKernelModuleDG R D E P))
      (dgNerve.map (dgPerfectToProjective R D) ≫
        dgModuleResolvedInfinity R (ProjectiveDGModules R D) E
          (dgProjectiveKernelModuleDG R D E P)) := by
  have e := dgModuleResolvedInfinity_precompIso R (PerfectDGModule R D)
    (ProjectiveDGModules R D) E (dgPerfectToProjective R D) (dgProjectiveKernelModuleDG R D E P)
  rw [dgProjectiveKernelModuleDG_perfect] at e
  exact e
end SerrePositivity.InfinityCategories
