module
public import SerrePositivity.InfinityCategories.Derived.FunctorHomIsIsoTransport
public import SerrePositivity.InfinityCategories.Derived.DGBimoduleResolvedMapInvertible
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeKernelBimoduleQuasiIso
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedHomRawFactor
public import SerrePositivity.InfinityCategories.Derived.FunctorHomTypedMapBridges
/-!
概要：双加群の準同型を、元の導来作用が同じ可逆な全関手射へ送る。
方針：半自由入力上の同じ tensor 射を分解で反転し、raw 比較から戻す。
規約：射の全射性・原 Hom 平坦性・出力の射影性は不要。使われ方：模型変更。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
lemma dgKernelResolvedRawFunctorHomFunctor_map_isIso_of_quasiIso
    {P Q : BimoduleCategory R E D} (f : P ⟶ Q)
    (hf : BimoduleCategory.quasiIso R E D f) :
    IsIso ((dgKernelResolvedRawFunctorHomFunctor R D E).map f) := by
  let I := dgFullSubcategoryInclusion R (RightModule R D) (dgModuleSemifreeProperty R D)
  let b := BimoduleTensor.composeMap R E D (SemifreeDGModules R D) f
    (𝟙 (BimoduleCategory.of R D (SemifreeDGModules R D) I))
  let p := dgNerve.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D P))
  let q := dgNerve.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D Q))
  let S := dgNerve.map I
  let L := dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule R E))
  let F := (BimoduleTensor.compose R E D (SemifreeDGModules R D)
    (BimoduleCategory.underlying R E D P) I).toFunctor
  let G := (BimoduleTensor.compose R E D (SemifreeDGModules R D)
    (BimoduleCategory.underlying R E D Q) I).toFunctor
  have hp : dgNerve.map F = S ≫ p := by
    simpa only [dgNerve.map_comp] using! congrArg (fun K => dgNerve.map K)
      (dgKernelTensor_postcomp_bimodule_eq R D E (SemifreeDGModules R D) I
        (BimoduleCategory.underlying R E D P)).symm
  have hq : dgNerve.map G = S ≫ q := by
    simpa only [dgNerve.map_comp] using! congrArg (fun K => dgNerve.map K)
      (dgKernelTensor_postcomp_bimodule_eq R D E (SemifreeDGModules R D) I
        (BimoduleCategory.underlying R E D Q)).symm
  have hb := dgBimoduleFunctorHomFunctor_resolvedMap_isIso_of_quasiIso
    R E (SemifreeDGModules R D) b (dgSemifreeKernelBimoduleMap_quasiIso R D E f hf)
  have hm := dgKernelBimoduleMap_precomp_nerve_hom_heq
    R D E (SemifreeDGModules R D) f I
  have he : HEq ((dgBimoduleFunctorHomFunctor R E (SemifreeDGModules R D)).map b)
      (functorHomPrecomp p q S ((dgKernelTensorFunctorHomFunctor R D E).map f)) :=
    hm.trans (functorHomPrecomp_map_heq p q S
      ((dgKernelTensorFunctorHomFunctor R D E).map f)).symm
  change IsIso (functorHomPostcomp (S ≫ p) (S ≫ q) L
    (functorHomPrecomp p q S ((dgKernelTensorFunctorHomFunctor R D E).map f)))
  exact functorHomPostcomp_isIso_of_heq
    (functorHomPrecomp p q S ((dgKernelTensorFunctorHomFunctor R D E).map f))
    ((dgBimoduleFunctorHomFunctor R E (SemifreeDGModules R D)).map b)
    hp.symm hq.symm he.symm L hb
lemma dgKernelDerivedFunctorHomFunctor_map_isIso_of_quasiIso
    {P Q : BimoduleCategory R E D} (f : P ⟶ Q)
    (hf : BimoduleCategory.quasiIso R E D f) :
    IsIso ((dgKernelDerivedFunctorHomFunctor R D E).map f) := by
  exact (NatIso.isIso_map_iff (dgKernelDerivedRawFactorNatIso R D E) f).mpr
    (dgKernelResolvedRawFunctorHomFunctor_map_isIso_of_quasiIso R D E f hf)
end
end SerrePositivity.InfinityCategories
