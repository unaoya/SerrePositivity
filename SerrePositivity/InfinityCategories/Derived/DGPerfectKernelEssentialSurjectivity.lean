module
public import SerrePositivity.InfinityCategories.Derived.DGPerfectKernelInfinity
/-!
概要：元の実 kernel 分解の preimage から、perfect 出力の本質的全射性を得る。
方針：元の全単体作用・実入力切断と perfect 性の保存反映を使う。
規約：高次 Hom の検査を省かない。使われ方：一般 Morita の Perf の結論。
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
/-- 元の一般 kernel の実 perfect 出力による比較。 -/
lemma dgPerfectKernelResolutionReplacement_onHomotopy_essSurj
    (P : Bimodule R E D) [(Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence] :
    (dgPerfectKernelResolutionReplacement R D E P).onHomotopy.EssSurj := by
  let F := dgSemifreeKernelModuleDG R D E P
  let G := dgModuleFunctorResolutionReplacement R (SemifreeDGModules R D) E F
  have : G.onHomotopy.IsEquivalence :=
    dgKernelResolutionReplacement_onHomotopy_isEquivalence R D E P
  refine ⟨fun Y => ?_⟩
  let y : PerfectDGModule R E := ForgetEnrichment.to (Complex R) Y.as
  obtain ⟨N, π, _, hπ⟩ := dgSemifreeModule_resolution_exists R E y.val
  let NH := (toHomotopy R (SemifreeDGModules R E)).obj (ForgetEnrichment.of (Complex R) N)
  let XH := G.onHomotopy.objPreimage NH
  let X : DGModuleFunctorResolutionObject R (SemifreeDGModules R D) E F :=
    ForgetEnrichment.to (Complex R) XH.as
  let e := G.onHomotopy.objObjPreimageIso NH
  have hi : IsIso ((moduleToDerived R E).map π) := moduleToDerived_inverts R E π hπ
  have hN := (modulePerfect R E).prop_of_iso (asIso ((moduleToDerived R E).map π)).symm
    y.property.2
  have hNH := (modulePerfect R E).prop_of_iso
    ((moduleToHomotopyDerivedIso R E).app (ForgetEnrichment.of (Complex R) N.val)).symm hN
  have hX := (modulePerfect R E).prop_of_iso
    ((dgSemifreeModuleToDerived R E).mapIso e).symm hNH
  have hS := (dgKernelResolution_perfect_iff R D E P XH).mp hX
  have hS' := (modulePerfect R D).prop_of_iso
    ((moduleToHomotopyDerivedIso R D).app (ForgetEnrichment.of (Complex R) X.source.val)) hS
  let xp : PerfectDGModule R D := ⟨X.source.val,
    dgSemifreeModule_isProjective R D X.source, hS'⟩
  let Z : DGModuleFunctorResolutionObject R (PerfectDGModule R D) E
      (dgPerfectKernelModuleDG R D E P) :=
    { source := xp
      replacement := X.replacement
      augmentation := X.augmentation
      surjective := X.surjective
      quasiIso := X.quasiIso }
  let ZH := (toHomotopy R _).obj (ForgetEnrichment.of (Complex R) Z)
  let J := perfectDGModuleInclusion R E Set.univ
  let I := dgFullSubcategoryInclusion R (RightModule R E) (dgModuleSemifreeProperty R E)
  have hπh : IsIso ((moduleToHomotopy R E).map π) :=
    moduleHomotopicallyProjective_quasiIso_isIso_homotopy R E
      (dgSemifreeModule_isProjective R E N) y.property.1 π hπ
  let ei := I.onHomotopy.mapIso e
  let ep := asIso ((moduleToHomotopy R E).map π)
  have ea : J.onHomotopy.obj
      ((dgPerfectKernelResolutionReplacement R D E P).onHomotopy.obj ZH) ≅
      J.onHomotopy.obj Y :=
    ei ≪≫ ep
  exact ⟨ZH, ⟨(Functor.FullyFaithful.ofFullyFaithful J.onHomotopy).preimageIso ea⟩⟩
/-- 元の一般 kernel の実 perfect 出力による比較。 -/
lemma dgPerfectKernelInfinity_isEssentiallySurjective
    (P : Bimodule R E D) [(Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence] :
    IsEssentiallySurjective (dgPerfectKernelInfinity R D E P) := by
  exact (dgModuleResolvedSourceSection_isQCatEquivalence R (PerfectDGModule R D) E
    (dgPerfectKernelModuleDG R D E P)).choose.isEssentiallySurjective.comp
      (dgNerve_map_isEssentiallySurjective (dgPerfectKernelResolutionReplacement R D E P)
        (dgPerfectKernelResolutionReplacement_onHomotopy_essSurj R D E P))
end SerrePositivity.InfinityCategories
