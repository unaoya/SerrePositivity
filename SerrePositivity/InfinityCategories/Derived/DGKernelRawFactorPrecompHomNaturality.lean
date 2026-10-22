module
public import SerrePositivity.InfinityCategories.Derived.DGKernelRawFactorHomNaturality
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoPrecompNaturalitySquare
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
variable (R : Type u) [CommRing R] (D E K : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R K] [Small.{u} K]
variable (P : BimoduleCategory R E D) {Q0 Q1 : BimoduleCategory R K E} (g : Q0 ⟶ Q1)
local notation "p" => BimoduleCategory.underlying R E D P
local notation "q0" => BimoduleCategory.underlying R K E Q0
local notation "q1" => BimoduleCategory.underlying R K E Q1
local notation "H0" => Morita.kernelTensor R E K q0
local notation "H1" => Morita.kernelTensor R E K q1
local notation "KP" => Morita.kernelTensor R D E p
local notation "C0" => Morita.kernelTensor R D K (BimoduleTensor.compose R K E D q0 p)
local notation "C1" => Morita.kernelTensor R D K (BimoduleTensor.compose R K E D q1 p)
local notation "I" => dgFullSubcategoryInclusion R (RightModule R D)
  (dgModuleSemifreeProperty R D)
local notation "J" => dgSemifreeKernelModuleDG R D E p
local notation "L" => dgModuleResolvedInfinity R (RightModule R K) K
  (DGFunctor.id (RightModule R K))
lemma dgKernelDerived_rawFactor_precomp_hom_naturality :
    ((dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R E) K (dgSemifreeKernelModuleDG
    R E K q0)).precomp (dgKernelDerivedInfinity R D E p)).hom ≫ (functorHomPrecomp (dgNerve.map
    ((dgFullSubcategoryInclusion R (RightModule R E) (dgModuleSemifreeProperty R E)).comp H0) ≫ L)
    (dgNerve.map ((dgFullSubcategoryInclusion R (RightModule R E) (dgModuleSemifreeProperty R
    E)).comp H1) ≫ L) (dgKernelDerivedInfinity R D E p) (dgModuleRawOutputPrecompHom R E K
    (SemifreeDGModules R E) (dgFullSubcategoryInclusion R (RightModule R E)
    (dgModuleSemifreeProperty R E)) H0 H1 (functorHomPostcomp (dgNerve.map H0) (dgNerve.map H1) L
    ((dgKernelTensorFunctorHomFunctor R E K).map g)))) = (functorHomPrecomp
    (dgKernelDerivedInfinity R E K q0) (dgKernelDerivedInfinity R E K q1) (dgKernelDerivedInfinity
    R D E p) ((dgKernelDerivedFunctorHomFunctor R E K).map g)) ≫
    ((dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R E) K (dgSemifreeKernelModuleDG
    R E K q1)).precomp (dgKernelDerivedInfinity R D E p)).hom := by
  let IE := dgFullSubcategoryInclusion R (RightModule R E) (dgModuleSemifreeProperty R E)
  let dg := functorHomPostcomp (dgNerve.map H0) (dgNerve.map H1) L
    ((dgKernelTensorFunctorHomFunctor R E K).map g)
  let di := dgModuleRawOutputPrecompHom R E K (SemifreeDGModules R E) IE H0 H1 dg
  let r0 := dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R E) K
    (dgSemifreeKernelModuleDG R E K q0)
  let r1 := dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R E) K
    (dgSemifreeKernelModuleDG R E K q1)
  let a0 := r0.precomp (dgKernelDerivedInfinity R D E p)
  let a1 := r1.precomp (dgKernelDerivedInfinity R D E p)
  have hq := dgKernelDerived_rawFactor_hom_naturality R E K g
  have ha := functorHomPrecomp_iso_square_forward r0 r1
    ((dgKernelDerivedFunctorHomFunctor R E K).map g) di
    (dgKernelDerivedInfinity R D E p) hq
  exact ha
end SerrePositivity.InfinityCategories
