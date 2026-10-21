module
public import SerrePositivity.InfinityCategories.Derived.DGModuleOutputUnliftedPrecomp
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedInfinity
/-!
概要：元の nerve 上の出力分解を実入力切断と半自由出力射影へ戻し、前合成と比較する。
方針：出力の対象宇宙の上げ下げを相殺し、同じ全関手同型を後合成する。
規約：元の出力の射影性は不要。使われ方：一般 kernel の Perf 包含比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (A C : Type (max (u + 1) v)) [DGCategory R A] [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E]
/-- 同じ実入力切断と半自由出力射影による全関手比較。 -/
lemma dgModuleResolvedInfinity_eq_section_replacement
    (F : DGFunctor R C (RightModule R E)) :
    dgModuleResolvedInfinity R C E F =
      dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C) ≫
        (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv ≫
          dgNerve.map (dgModuleFunctorResolutionReplacement R C E F) := by
  have hE := congrArg (fun H => dgNerve.map H)
    (dgUniverseLiftUp_comp_down.{u, max (u + 1) v, max (u + 1) v} R
      (SemifreeDGModules R E))
  simp only [dgNerve.map_comp, dgNerve.map_id] at hE
  simp only [dgModuleResolvedInfinity, dgModuleOutputResolutionInfinity,
    dgModuleFunctorResolutionReplacementLift, dgNerve.map_comp, Category.assoc,
    hE, Category.comp_id]
/-- 同じ実入力切断と半自由出力射影による全関手比較。 -/
def dgModuleResolvedInfinity_precompIso
    (H : DGFunctor R A C) (F : DGFunctor R C (RightModule R E)) :
    FunctorIso (dgModuleResolvedInfinity R A E (H.comp F))
      (dgNerve.map H ≫ dgModuleResolvedInfinity R C E F) := by
  have e := (dgModuleOutputResolution_unliftedPrecompIso.{u, v, v} R A C E H F).postcomp
    (dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
      (SemifreeDGModules R E)))
  simpa only [dgModuleResolvedInfinity, Category.assoc] using! e
/-- 元の入力宇宙での実切断は、全 ∞ 圏の同値。 -/
lemma dgModuleResolvedSourceSection_isQCatEquivalence
    (F : DGFunctor R C (RightModule R E)) :
    IsQCatEquivalence
      (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C) ≫
        (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv) := by
  let U := dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C
  let V := dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C
  let i : dgNerve R C ≅
      dgNerve R (DGUniverseLift.{max (u + 1) v, max (u + 1) v} C) :=
    { hom := dgNerve.map U
      inv := dgNerve.map V
      hom_inv_id := by
        rw [← dgNerve.map_comp, dgUniverseLiftUp_comp_down, dgNerve.map_id]
      inv_hom_id := by
        rw [← dgNerve.map_comp, dgUniverseLiftDown_comp_up, dgNerve.map_id] }
  exact (qCatEquivalenceOfIso i).isQCatEquivalence.comp
    (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).symm.isQCatEquivalence
end SerrePositivity.InfinityCategories
