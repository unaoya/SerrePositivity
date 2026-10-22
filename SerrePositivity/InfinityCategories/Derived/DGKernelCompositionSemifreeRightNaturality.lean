module
public import SerrePositivity.InfinityCategories.Derived.DGKernelCompositionNerveRightNaturality
public import SerrePositivity.InfinityCategories.Derived.DGKernelCompositionSemifreeHomTransport
public import SerrePositivity.InfinityCategories.Derived.FunctorHomWhiskeredSquareTransport
public import SerrePositivity.InfinityCategories.Derived.DGModuleRawOutputPrecompHom
/-!
概要：通常 tensor の右変数自然性を半自由入力と同じ出力分解へ移す。
方針：元の指定比較の射と端点輸送済み raw 作用を全関手の四角形で照合する。
規約：後続 kernel の平坦性を要求しない。使われ方：元の κ の右変数自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
local notation "F" => dgSemifreeKernelModuleDG R D E p
local notation "L" => dgModuleResolvedInfinity R (RightModule R K) K
  (DGFunctor.id (RightModule R K))
lemma dgKernelTensorCompositionSemifreeIso_right_naturality
    : ((dgKernelTensorCompositionSemifreeIso R D E K p q0).postcomp L).hom ≫
      dgModuleRawOutputPrecompHom R D K (SemifreeDGModules R D) I C0 C1
        (functorHomPostcomp (dgNerve.map C0) (dgNerve.map C1) L
          ((dgKernelTensorFunctorHomFunctor R D K).map
            (BimoduleTensor.composeMap R K E D g (𝟙 P)))) =
      dgModuleRawOutputPrecompHom R E K (SemifreeDGModules R D) F H0 H1
        (functorHomPostcomp (dgNerve.map H0) (dgNerve.map H1) L
          ((dgKernelTensorFunctorHomFunctor R E K).map g)) ≫
        ((dgKernelTensorCompositionSemifreeIso R D E K p q1).postcomp L).hom := by
  let delta : FunctorHom (dgNerve.map C0) (dgNerve.map C1) :=
    (dgKernelTensorFunctorHomFunctor R D K).map
      (BimoduleTensor.composeMap R K E D g (𝟙 P))
  let gamma : FunctorHom (dgNerve.map H0) (dgNerve.map H1) :=
    (dgKernelTensorFunctorHomFunctor R E K).map g
  have hn := dgKernelTensorCompositionNerveIso_right_naturality R D E K P g
  have hs := functorHom_precomp_postcomp_square
    (dgKernelTensorCompositionNerveIso R D E K p q0).hom delta
    (functorHomPrecomp (dgNerve.map H0) (dgNerve.map H1) (dgNerve.map KP) gamma)
    (dgKernelTensorCompositionNerveIso R D E K p q1).hom hn (dgNerve.map I) L
  have hc0 := dgKernelTensorCompositionSemifreeIso_postcomp_hom_heq R D E K p q0
  have hc1 := dgKernelTensorCompositionSemifreeIso_postcomp_hom_heq R D E K p q1
  have hr0 := dgModuleRawOutputPrecompHom_heq R D K (SemifreeDGModules R D)
    I C0 C1 (functorHomPostcomp (dgNerve.map C0) (dgNerve.map C1) L delta)
  have hr := hr0.trans (heq_of_eq (functorHomPrecomp_postcomp
    (dgNerve.map C0) (dgNerve.map C1) (dgNerve.map I) L delta).symm)
  have hq0 := dgModuleRawOutputPrecompHom_heq R E K (SemifreeDGModules R D)
    F H0 H1 (functorHomPostcomp (dgNerve.map H0) (dgNerve.map H1) L gamma)
  have hq := hq0.trans (functorHom_precomp_postcomp_associative_heq
    gamma (dgNerve.map I) (dgNerve.map KP) (dgNerve.map F) L
    (dgNerve.map_comp I KP))
  have hsource (Q : Bimodule R K E) :=
    congrArg (fun t => t ≫ L) (dgKernelTensorCompositionSemifreeIso_source_eq R D E K p Q)
  have htarget (Q : Bimodule R K E) :=
    congrArg (fun t => t ≫ L) (dgKernelTensorCompositionSemifreeIso_target_eq R D E K p Q)
  exact functorHom_two_two_eq_of_heq _ _ _ _ _ _ _ _
    (hsource q0) (htarget q0) (hsource q1) (htarget q1) hc0 hr hq hc1 hs
end
end SerrePositivity.InfinityCategories
