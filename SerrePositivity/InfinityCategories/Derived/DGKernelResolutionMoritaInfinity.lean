module
public import SerrePositivity.InfinityCategories.Derived.DGResolutionHomologyDetection
public import SerrePositivity.InfinityCategories.Derived.DGKernelResolutionHomotopyMorita
public import SerrePositivity.InfinityCategories.Stable.ExactFunctorChoice
/-!
概要：一般双加群の主導来 Morita 同値を、元の実半自由 ∞ 関手の同値へ昇格する。
方針：実分解圏の H⁰ 同値、斉次 shift による全 Hom 検査、実入力切断を合成する。
規約：出力の射影性や局所 Hom の平坦性は追加しない。使われ方：β5 e の D の結論。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 同じ一般 kernel の主導来同値を実半自由模型へ移す。 -/
lemma dgKernelResolutionReplacement_homQuasiIso
    (P : Bimodule R E D) [(Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence] :
    HomQuasiIso (dgModuleFunctorResolutionReplacement R (SemifreeDGModules R D) E
      (dgSemifreeKernelModuleDG R D E P)) := by
  have := dgKernelResolutionReplacement_onHomotopy_isEquivalence R D E P
  exact dgModuleResolution_homQuasiIso_of_ho R D E _ _ _
/-- 同じ一般 kernel の主導来同値を実半自由模型へ移す。 -/
lemma dgKernelResolutionReplacement_quasiEquivalence
    (P : Bimodule R E D) [(Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence] :
    QuasiEquivalence (dgModuleFunctorResolutionReplacement R (SemifreeDGModules R D) E
      (dgSemifreeKernelModuleDG R D E P)) := by
  have := dgKernelResolutionReplacement_onHomotopy_isEquivalence R D E P
  exact ⟨dgKernelResolutionReplacement_homQuasiIso R D E P, inferInstance⟩
/-- 同じ一般 kernel の主導来同値を実半自由模型へ移す。 -/
lemma dgKernelDerivedInfinity_isQCatEquivalence_of_classical
    (P : Bimodule R E D) [(Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence] :
    IsQCatEquivalence (dgKernelDerivedInfinity R D E P) := by
  let F := dgSemifreeKernelModuleDG R D E P
  let G := dgModuleFunctorResolutionReplacement R (SemifreeDGModules R D) E F
  have hG : IsQCatEquivalence (dgNerve.map G) :=
    dgNerve_map_isQCatEquivalence_of_quasiEquivalence G
      (dgKernelResolutionReplacement_quasiEquivalence R D E P)
  let U := dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (SemifreeDGModules R D)
  let V := dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R (SemifreeDGModules R D)
  let i : dgNerve R (SemifreeDGModules R D) ≅
      dgNerve R (DGUniverseLift.{max (u + 1) v, max (u + 1) v} (SemifreeDGModules R D)) :=
    { hom := dgNerve.map U
      inv := dgNerve.map V
      hom_inv_id := by
        rw [← dgNerve.map_comp, dgUniverseLiftUp_comp_down, dgNerve.map_id]
      inv_hom_id := by
        rw [← dgNerve.map_comp, dgUniverseLiftDown_comp_up, dgNerve.map_id] }
  have hS := (dgModuleFunctorResolutionSourceNerveEquivalence R
    (SemifreeDGModules R D) E F).symm.isQCatEquivalence
  have h := (qCatEquivalenceOfIso i).isQCatEquivalence.comp (hS.comp hG)
  change IsQCatEquivalence (dgNerve.map U ≫
    (dgModuleFunctorResolutionSourceNerveEquivalence R
      (SemifreeDGModules R D) E F).inv ≫ dgNerve.map G) at h
  have hE := congrArg (fun H => dgNerve.map H)
    (dgUniverseLiftUp_comp_down.{u, max (u + 1) v, max (u + 1) v} R
      (SemifreeDGModules R E))
  simp only [dgNerve.map_comp, dgNerve.map_id] at hE
  simpa only [dgKernelDerivedInfinity, dgModuleOutputResolutionInfinity,
    dgModuleFunctorResolutionReplacementLift, dgNerve.map_comp, Category.assoc,
    hE, Category.comp_id, U, F, G] using h
/-- 同じ一般 kernel の主導来同値を実半自由模型へ移す。 -/
lemma dgKernelDerivedInfinity_isExactFunctor_of_classical
    (P : Bimodule R E D) [(Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence] :
    IsExactFunctor (dgKernelDerivedInfinity R D E P) :=
  isExactFunctor_of_isQCatEquivalence
    (dgKernelDerivedInfinity_isQCatEquivalence_of_classical R D E P)
end SerrePositivity.InfinityCategories
