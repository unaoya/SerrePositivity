module
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeProjectiveEquivalence
public import SerrePositivity.InfinityCategories.Derived.DGClosedModuleFunctorExact
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementOperations
/-!
概要：任意の小さい dg 圏の Perf の実安定 ∞ 圏と、D(D) への実完全充満忠実関手。
方針：既存の射影的 perfect dg 加群を全 Hom end ごと使い、標準演算の閉性を証明する。
規約：冪等完備性は別工程。使われ方：β5 の Perf(A) の模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
/-- 射影的 perfect 加群の実 dg nerve による Perf の模型。 -/
abbrev dgModulePerfectInfinityCategory := dgNerve R (PerfectDGModule R D)
/-- 既存の射影的 perfect 条件は、実零・標準 cone・fiber で閉じる。 -/
lemma dgModulePerfectProperty_closed :
    DGModuleClosedProperty R D (modulePerfectProjectiveOver R D Set.univ) where
  zero := modulePerfectProjectiveOver_zero R D Set.univ
  cone f hM hN := modulePerfectProjectiveOver_cone R D hM hN f
  fiber f hM hN := modulePerfectProjectiveOver_shift R D
    (modulePerfectProjectiveOver_cone R D hM hN f) (-1)
/-- Perf の実 dg nerve は安定。 -/
theorem dgModulePerfectInfinityCategory_isStable : IsStable (dgModulePerfectInfinityCategory R D) :=
  dgClosedModule_isStable R D _ (dgModulePerfectProperty_closed R D)
/-- 実 perfect 加群から全射影的加群への、同じ全 Hom end の dg 包含。 -/
def dgPerfectToProjective : DGFunctor R (PerfectDGModule R D) (ProjectiveDGModules R D) :=
  dgFullFunctorRestriction R (RightModule R D) (RightModule R D)
    (DGFunctor.id (RightModule R D)) _ _ (fun _ h => h.1)
/-- 実 perfect 加群から射影的模型への dg 包含の nerve は完全。 -/
lemma dgPerfectToProjectiveNerve_isExactFunctor :
    IsExactFunctor (dgNerve.map (dgPerfectToProjective R D)) :=
  dgClosedModuleFunctorNerve_isExactFunctor R D D (DGFunctor.id (RightModule R D)) _ _
    (dgModulePerfectProperty_closed R D) (fun _ h => h.1)
/-- Perf から半自由模型の D(D) への実 ∞ 関手。 -/
def dgPerfectInclusionInfinity : dgModulePerfectInfinityCategory R D ⟶
    dgModuleDerivedInfinityCategory R D :=
  dgNerve.map (dgPerfectToProjective R D) ≫
    (dgSemifreeToProjectiveNerve_isQCatEquivalence R D).choose.inv
/-- Perf の実 ∞ 関手は完全。 -/
theorem dgPerfectInclusionInfinity_isExactFunctor :
    IsExactFunctor (dgPerfectInclusionInfinity R D) := by
  let := dgPerfectToProjectiveNerve_isExactFunctor R D
  have hi := isExactFunctor_of_isQCatEquivalence
    (dgSemifreeToProjectiveNerve_isQCatEquivalence R D).choose.symm.isQCatEquivalence
  change IsExactFunctor (dgSemifreeToProjectiveNerve_isQCatEquivalence R D).choose.inv at hi
  exact isExactFunctor_comp _ _
/-- Perf の実 ∞ 関手は、全写像空間で充満忠実。 -/
theorem dgPerfectInclusionInfinity_isFullyFaithful :
    IsFullyFaithful (dgPerfectInclusionInfinity R D) := by
  have hg : IsFullyFaithful (dgNerve.map (dgPerfectToProjective R D)) := by
    apply dgNerve_map_isFullyFaithful_of_homIso
    intro M N
    change IsIso (𝟙 (moduleHom R D M.val N.val))
    infer_instance
  have hi := (dgSemifreeToProjectiveNerve_isQCatEquivalence R D).choose.symm.isQCatEquivalence
  change IsQCatEquivalence (dgSemifreeToProjectiveNerve_isQCatEquivalence R D).choose.inv at hi
  exact hg.comp hi.isFullyFaithful
end SerrePositivity.InfinityCategories
