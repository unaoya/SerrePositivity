module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelDerivedRawPrecompAction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.IsoRawFactorSquare
/-!
概要：元の導来 kernel の raw factor と augmentation の任意射自然性を照合する。
方針：同じ比較と実射作用を保ち、全前合成・同じ指定切断上の四角形を使う。
規約：後続 kernel の平坦性・射の可逆性を要求しない。使われ方：元の κ の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalClosed
variable (R : Type u) [CommRing R]
lemma dgKernelDerived_rawFactor_hom_naturality
    (E K : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] [_root_.SerrePositivity.DifferentialGraded.DGCategory R K] [Small.{u} K]
    {Q0 Q1 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R K E} (g : Q0 ⟶ Q1) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E) K
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R E K (BimoduleCategory.underlying R K E Q0))).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleRawOutputPrecompHom R E K (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E)
        (dgFullSubcategoryInclusion R (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E))
        (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R E K (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R K E Q0))
        (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R E K (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R K E Q1))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E K (BimoduleCategory.underlying R K E Q0)))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E K (BimoduleCategory.underlying R K E Q1)))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K)))
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R E K).map g)) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R E K).map g ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E) K
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R E K (BimoduleCategory.underlying R K E Q1))).hom := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.iso_conjugation_hom_square _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor_map_rawPrecomp R E K g)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
