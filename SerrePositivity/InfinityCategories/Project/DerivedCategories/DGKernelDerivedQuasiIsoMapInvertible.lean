module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomIsIsoTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGBimoduleResolvedMapInvertible
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSemifreeKernelBimoduleQuasiIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelDerivedHomRawFactor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomTypedMapBridges
/-!
概要：双加群の準同型を、元の導来作用が同じ可逆な全関手射へ送る。
方針：半自由入力上の同じ tensor 射を分解で反転し、raw 比較から戻す。
規約：射の全射性・原 Hom 平坦性・出力の射影性は不要。使われ方：模型変更。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
lemma dgKernelResolvedRawFunctorHomFunctor_map_isIso_of_quasiIso
    {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (f : P ⟶ Q)
    (hf : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R E D f) :
    IsIso ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelResolvedRawFunctorHomFunctor R D E).map f) := by
  let I := dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)
  let b := BimoduleTensor.composeMap R E D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) f
    (𝟙 (BimoduleCategory.of R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) I))
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D P))
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D Q))
  let S := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map I
  let L := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule R E))
  let F := (BimoduleTensor.compose R E D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P) I).toFunctor
  let G := (BimoduleTensor.compose R E D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D Q) I).toFunctor
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F = S ≫ p := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp] using! congrArg (fun K => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map K)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensor_postcomp_bimodule_eq R D E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) I
        (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P)).symm
  have hq : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G = S ≫ q := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp] using! congrArg (fun K => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map K)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensor_postcomp_bimodule_eq R D E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) I
        (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D Q)).symm
  have hb := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor_resolvedMap_isIso_of_quasiIso
    R E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) b (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelBimoduleMap_quasiIso R D E f hf)
  have hm := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelBimoduleMap_precomp_nerve_hom_heq
    R D E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) f I
  have he : HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)).map b)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp p q S ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R D E).map f)) :=
    hm.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_map_heq p q S
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R D E).map f)).symm
  change IsIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (S ≫ p) (S ≫ q) L
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp p q S ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R D E).map f)))
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_isIso_of_heq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp p q S ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R D E).map f))
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)).map b)
    hp.symm hq.symm he.symm L hb
lemma dgKernelDerivedFunctorHomFunctor_map_isIso_of_quasiIso
    {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (f : P ⟶ Q)
    (hf : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R E D f) :
    IsIso ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map f) := by
  exact (NatIso.isIso_map_iff (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedRawFactorNatIso R D E) f).mpr
    (dgKernelResolvedRawFunctorHomFunctor_map_isIso_of_quasiIso R D E f hf)
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
