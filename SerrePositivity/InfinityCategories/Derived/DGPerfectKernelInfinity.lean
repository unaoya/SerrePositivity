module
public import SerrePositivity.InfinityCategories.Derived.DGPerfectKernelResolution
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedPrecomposition
/-!
概要：一般 kernel の実 perfect 入力と同じ半自由出力から Perf の ∞ 関手を構成する。
方針：実入力射影の指定逆と、perfect 出力射影の dg nerve を合成する。
規約：全単体上の実作用。使われ方：一般 Morita 同値の Perf への制限。
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
/-- 同じ実入力切断による perfect 出力の全単体作用。 -/
def dgPerfectKernelInfinity
    (P : Bimodule R E D) [(Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence] :
    dgModulePerfectInfinityCategory R D ⟶ dgModulePerfectInfinityCategory R E :=
  dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (PerfectDGModule R D)) ≫
    (dgModuleFunctorResolutionSourceNerveEquivalence R (PerfectDGModule R D) E
      (dgPerfectKernelModuleDG R D E P)).inv ≫
        dgNerve.map (dgPerfectKernelResolutionReplacement R D E P)
/-- 同じ実入力切断による perfect 出力の全単体作用。 -/
def dgPerfectKernelInfinity_resolvedInclusionIso
    (P : Bimodule R E D) [(Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence] :
    FunctorIso (dgPerfectKernelInfinity R D E P ≫ dgPerfectInclusionInfinity R E)
      (dgModuleResolvedInfinity R (PerfectDGModule R D) E (dgPerfectKernelModuleDG R D E P)) := by
  let F := dgPerfectKernelModuleDG R D E P
  let G := dgModuleFunctorResolutionReplacement R (PerfectDGModule R D) E F
  let L := dgPerfectKernelResolutionReplacement R D E P
  have hd := congrArg (fun H => dgNerve.map H)
    (dgPerfectKernelResolutionReplacement_projective R D E P)
  simp only [dgNerve.map_comp] at hd
  have h0 : FunctorIso (dgNerve.map L ≫ dgPerfectInclusionInfinity R E) (dgNerve.map G) := by
    change FunctorIso ((dgNerve.map L ≫ dgNerve.map (dgPerfectToProjective R E)) ≫
      (dgSemifreeToProjectiveNerve_isQCatEquivalence R E).choose.inv) _
    rw [hd]
    simpa only [Category.assoc, Category.comp_id] using!
      (dgSemifreeToProjectiveNerve_isQCatEquivalence R E).choose.homInvIso.precomp (dgNerve.map G)
  have h := h0.precomp
    (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R
      (PerfectDGModule R D)) ≫
      (dgModuleFunctorResolutionSourceNerveEquivalence R (PerfectDGModule R D) E F).inv)
  simpa only [dgPerfectKernelInfinity, dgModuleResolvedInfinity_eq_section_replacement,
    Category.assoc, F, G, L] using! h
end SerrePositivity.InfinityCategories
