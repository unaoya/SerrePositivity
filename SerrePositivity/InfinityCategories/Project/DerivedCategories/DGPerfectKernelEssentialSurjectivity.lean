module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPerfectKernelInfinity
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 元の一般 kernel の実 perfect 出力による比較。 -/
lemma dgPerfectKernelResolutionReplacement_onHomotopy_essSurj
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) [(_root_.SerrePositivity.DifferentialGraded.Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence] :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectKernelResolutionReplacement R D E P).onHomotopy.EssSurj := by
  let F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P
  let G := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E F
  have : G.onHomotopy.IsEquivalence :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelResolutionReplacement_onHomotopy_isEquivalence R D E P
  refine ⟨fun Y => ?_⟩
  let y : PerfectDGModule R E := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) Y.as
  obtain ⟨N, π, _, hπ⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModule_resolution_exists R E y.val
  let NH := (toHomotopy R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E)).obj (ForgetEnrichment.of (Complex R) N)
  let XH := G.onHomotopy.objPreimage NH
  let X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E F :=
    ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) XH.as
  let e := G.onHomotopy.objObjPreimageIso NH
  have hi : IsIso ((_root_.SerrePositivity.DifferentialGraded.moduleToDerived R E).map π) := _root_.SerrePositivity.DifferentialGraded.moduleToDerived_inverts R E π hπ
  have hN := (_root_.SerrePositivity.DifferentialGraded.modulePerfect R E).prop_of_iso (asIso ((_root_.SerrePositivity.DifferentialGraded.moduleToDerived R E).map π)).symm
    y.property.2
  have hNH := (_root_.SerrePositivity.DifferentialGraded.modulePerfect R E).prop_of_iso
    ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopyDerivedIso R E).app (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) N.val)).symm hN
  have hX := (_root_.SerrePositivity.DifferentialGraded.modulePerfect R E).prop_of_iso
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModuleToDerived R E).mapIso e).symm hNH
  have hS := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelResolution_perfect_iff R D E P XH).mp hX
  have hS' := (_root_.SerrePositivity.DifferentialGraded.modulePerfect R D).prop_of_iso
    ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopyDerivedIso R D).app (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) X.source.val)) hS
  let xp : PerfectDGModule R D := ⟨X.source.val,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModule_isProjective R D X.source, hS'⟩
  let Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R (PerfectDGModule R D) E
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectKernelModuleDG R D E P) :=
    { source := xp
      replacement := X.replacement
      augmentation := X.augmentation
      surjective := X.surjective
      quasiIso := X.quasiIso }
  let ZH := (_root_.SerrePositivity.DifferentialGraded.toHomotopy R _).obj (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) Z)
  let J := _root_.SerrePositivity.DifferentialGraded.perfectDGModuleInclusion R E Set.univ
  let I := dgFullSubcategoryInclusion R (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E)
  have hπh : IsIso ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy R E).map π) :=
    _root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective_quasiIso_isIso_homotopy R E
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModule_isProjective R E N) y.property.1 π hπ
  let ei := I.onHomotopy.mapIso e
  let ep := asIso ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy R E).map π)
  have ea : J.onHomotopy.obj
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectKernelResolutionReplacement R D E P).onHomotopy.obj ZH) ≅
      J.onHomotopy.obj Y :=
    ei ≪≫ ep
  exact ⟨ZH, ⟨(Functor.FullyFaithful.ofFullyFaithful J.onHomotopy).preimageIso ea⟩⟩
/-- 元の一般 kernel の実 perfect 出力による比較。 -/
lemma dgPerfectKernelInfinity_isEssentiallySurjective
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) [(_root_.SerrePositivity.DifferentialGraded.Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectKernelInfinity R D E P) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedSourceSection_isQCatEquivalence R (PerfectDGModule R D) E
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectKernelModuleDG R D E P)).choose.isEssentiallySurjective.comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_map_isEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectKernelResolutionReplacement R D E P)
        (dgPerfectKernelResolutionReplacement_onHomotopy_essSurj R D E P))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
