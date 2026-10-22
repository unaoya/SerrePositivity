module
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedRawPrecompAction
public import SerrePositivity.InfinityCategories.Derived.IsoRawFactorSquare
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
variable (R : Type u) [CommRing R]
lemma dgKernelDerived_rawFactor_hom_naturality
    (E K : Type v) [DGCategory R E] [Small.{u} E] [DGCategory R K] [Small.{u} K]
    {Q0 Q1 : BimoduleCategory R K E} (g : Q0 ⟶ Q1) :
    (dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R E) K
      (dgSemifreeKernelModuleDG R E K (BimoduleCategory.underlying R K E Q0))).hom ≫
      dgModuleRawOutputPrecompHom R E K (SemifreeDGModules R E)
        (dgFullSubcategoryInclusion R (RightModule R E) (dgModuleSemifreeProperty R E))
        (Morita.kernelTensor R E K (BimoduleCategory.underlying R K E Q0))
        (Morita.kernelTensor R E K (BimoduleCategory.underlying R K E Q1))
        (functorHomPostcomp
          (dgNerve.map (Morita.kernelTensor R E K (BimoduleCategory.underlying R K E Q0)))
          (dgNerve.map (Morita.kernelTensor R E K (BimoduleCategory.underlying R K E Q1)))
          (dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K)))
          ((dgKernelTensorFunctorHomFunctor R E K).map g)) =
      (dgKernelDerivedFunctorHomFunctor R E K).map g ≫
        (dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R E) K
          (dgSemifreeKernelModuleDG R E K (BimoduleCategory.underlying R K E Q1))).hom := by
  exact iso_conjugation_hom_square _ _ _ _
    (dgKernelDerivedFunctorHomFunctor_map_rawPrecomp R E K g)
end SerrePositivity.InfinityCategories
