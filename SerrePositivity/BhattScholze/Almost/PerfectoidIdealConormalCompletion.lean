module

public import SerrePositivity.BhattScholze.Almost.PerfectoidIdealLemma103
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteScalarConePurity
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedBaseChangeScalar
public import SerrePositivity.CategoryTheory.ExactDerivedTStructure

/-!
# perfectoid 化の核の conormal の導来完備化
## 概要
核 K の通常の conormal 加群 K/K² は p 作用が可逆であり、その導来 p 完備化は零である。
## 方針
Lemma 10.3 の商自己積を Koszul 錐へ移し、H⁻² の消滅から Tor₁ 上の p 単射性を得る。
## 規約
conormal の完備化と、導来自己テンソルの完備化を区別する。
## 使われ方
BS 著者版 Remark 10.7（印刷 p.80）の mod p 冪冪等性の中間結果を明示する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits HomologicalComplex SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R)

/--
## 概要
perfectoid 化の核 K の conormal 加群 K/K² 上の p 作用は全単射である。
## 方針
商自己積の完備化同型の Koszul 還元から単射性を得て、既存の Tor₁ 可除性と合成する。
## 規約
通常の conormal 加群に関する主張であり、p ねじれなしを追加仮定しない。
## 使われ方
BS 著者版 Remark 10.7（印刷 p.80）の導来完備化消滅を証明する。
-/
theorem perfectoidIdeal_conormal_smul_bijective :
    Function.Bijective (fun x : (perfectoidIdeal R p hR g).Cotangent => (p : R) • x) := by
  let I := perfectoidIdeal R p hR g
  let Q := ModuleCat.of R (R ⧸ I)
  let μ := boundedAboveDerivedAlgebraMul (R := R) (R ⧸ I)
  have hμ := (perfectoidIdeal_lemma103 R p hR g).2.1
  have hk : IsIso ((derivedScalarConeFunctor R (p : R)).map μ.hom) := by
    have hh := derivedScalarCone_map_isIso_of_completion R (p : R) μ.hom hμ 1
    rw [_root_.pow_one] at hh
    exact hh
  let L := (CochainComplex.singleFunctor (ModuleCat R) 0).obj Q
  have hl (i : ℤ) (hi : i ≠ 0) : IsZero (L.homology i) :=
    (derivedSingleHomology_isZero Q i hi).of_iso
      ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app L).symm
  have hzL : IsZero (((scalarConeFunctor (p : R)).obj L).homology (-2)) :=
    (Cone.exact₃ (smulId (p : R) L) (-2) (-1) (by omega)).isZero_of_both_isZero
      (hl (-2) (by omega)) (hl (-1) (by omega))
  have hzY : IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) (-2)).obj
      ((derivedScalarConeFunctor R (p : R)).obj
        ((boundedAboveDerivedSingleFunctor.obj Q).obj))) := hzL.of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat R) (-2)).mapIso
      ((derivedScalarConeComparison R (p : R)).app L) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat R) (-2)).app
        ((scalarConeFunctor (p : R)).obj L))
  have hzX := hzY.of_iso ((DerivedCategory.homologyFunctor (ModuleCat R) (-2)).mapIso
    (asIso ((derivedScalarConeFunctor R (p : R)).map μ.hom)))
  have hinj := derived_homology_smul_injective_of_scalarCone_isZero (p : R)
    ((boundedAboveDerivedTensorModuleFunctor Q).obj Q) (-1)
    (by simpa [boundedAboveDerivedTensorModuleFunctor, Q] using hzX)
  let e := (((boundedAboveDerivedTensorModuleTorNatIso Q 1).app Q).toLinearEquiv).trans
    (quotientTorOneConormalEquiv R I)
  constructor
  · intro x y hxy
    change (p : R) • x = (p : R) • y at hxy
    apply e.symm.injective
    apply hinj
    change (p : R) • e.symm x = (p : R) • e.symm y
    rw [← e.symm.map_smul, ← e.symm.map_smul, hxy]
  · exact (quotientTorOne_smul_surjective_iff_conormal R I (p : R)).mp
      (quotientTorOne_smul_surjective_of_completed_mul_isIso (p : R) I hμ)

/--
## 概要
perfectoid 化の核 K の通常の conormal 加群 K/K² の導来 p 完備化は零である。
## 方針
p 作用の全単射性を実完備化へ移す。その各ホモロジーは導来完備かつ p 可除なので零となる。
## 規約
G2 の元の完備化関手を degree zero の conormal 加群へ適用する。
## 使われ方
BS 著者版 Remark 10.7（印刷 p.80）の冪等性を導く中間結果を公開する。
-/
theorem perfectoidIdeal_conormal_completion_isZero :
    IsZero ((derivedComplexCompletionFunctor R (p : R)).obj
      ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj
        (ModuleCat.of R (perfectoidIdeal R p hR g).Cotangent))) := by
  let M := ModuleCat.of R (perfectoidIdeal R p hR g).Cotangent
  let X := (DerivedCategory.singleFunctor (ModuleCat R) 0).obj M
  let F := derivedComplexCompletionFunctor R (p : R)
  have hM : IsIso ((p : R) • 𝟙 M) := (ConcreteCategory.isIso_iff_bijective _).mpr
    (perfectoidIdeal_conormal_smul_bijective R p hR g)
  have hX : IsIso ((p : R) • 𝟙 X) := by
    have hh := (DerivedCategory.singleFunctor (ModuleCat R) 0).map_isIso ((p : R) • 𝟙 M)
    simpa only [Functor.map_smul, CategoryTheory.Functor.map_id] using hh
  have hF : IsIso ((p : R) • 𝟙 (F.obj X)) := by
    have hh := F.map_isIso ((p : R) • 𝟙 X)
    rwa [derivedCompletion_map_scalar_id] at hh
  apply (derived_isZero_iff_homology _).mpr
  intro i
  have hH : IsIso ((p : R) • 𝟙 ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
      (F.obj X))) := by
    have hh := (DerivedCategory.homologyFunctor (ModuleCat R) i).map_isIso
      ((p : R) • 𝟙 (F.obj X))
    simpa only [Functor.map_smul, CategoryTheory.Functor.map_id] using hh
  exact isZero_of_complete_of_smul_surjective (p : R) _
    (isComplete_homology_isModuleComplete R (p : R) (F.obj X)
      (derivedComplexCompletionFunctor_isComplete R (p : R) X) i)
    ((ConcreteCategory.isIso_iff_bijective _).mp hH).surjective

/--
## 概要
perfectoid 化の核 K の通常の conormal 加群を p で割ると零加群になる。
## 方針
p 作用の全射性で代表を p 倍に書き、通常の商写像が p 倍を消すことを使う。
## 規約
完備化後の H⁰ だけでなく、元の通常の conormal の mod p 商について主張する。
## 使われ方
BS 著者版 Remark 10.7（印刷 p.80）の K=K²+pK へ移る中間結果である。
-/
theorem perfectoidIdeal_conormal_mod_p_isZero :
    IsZero (modulePowerReduction (p : R)
      (ModuleCat.of R (perfectoidIdeal R p hR g).Cotangent) 1) := by
  let M := ModuleCat.of R (perfectoidIdeal R p hR g).Cotangent
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨m, rfl⟩ := (ModuleCat.epi_iff_surjective (modulePowerReductionMap (p : R) M 1)).mp
    (inferInstance) x
  obtain ⟨y, hy⟩ := (perfectoidIdeal_conormal_smul_bijective R p hR g).surjective m
  change (modulePowerReductionMap (p : R) M 1).hom m = 0
  rw [← hy, map_smul]
  simpa only [_root_.pow_one] using
    modulePowerReduction_pow_smul_zero (p : R) M 1
      ((modulePowerReductionMap (p : R) M 1) y)

end SerrePositivity.BhattScholze
