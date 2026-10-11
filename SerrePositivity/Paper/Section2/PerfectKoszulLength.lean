module

public import SerrePositivity.Paper.Section2.PerfectApproximationLength
public import SerrePositivity.Paper.Section2.TowerKoszulLength
public import SerrePositivity.HomologicalAlgebra.KoszulOrdinaryLength
public import SerrePositivity.CommutativeAlgebra.KoszulFiniteLength
public import SerrePositivity.Paper.Section2.TowerLengthOn

/-! # Perfection の近似環における Koszul ホモロジーの長さ

根の段の Frobenius 同型と剰余体の一致により、有限段のホモロジーの長さを
元の環上の Frobenius 冪の Koszul ホモロジーの長さに戻す。
-/

public section

universe u

namespace SerrePositivity.Section2

open IsLocalRing
open scoped ENNReal

attribute [local instance] rootStageAlgebra towerPerfectionAlgebra stagePerfectionAlgebra
  stageTowerPerfection

variable (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing D] [IsDomain D] [IsLocalRing D] [Algebra A D]
    (p : ℕ) [Fact p.Prime] [CharP D p]
    [CharP (ResidueField D) p] [PerfectField (ResidueField D)]
    {h : ℕ} (t : Fin h → A)
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (hdim : ringKrullDim A = h)
    (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))

include ht hdim hinj hres in
/-- 根の段で測った Koszul ホモロジーの長さを、Frobenius 同型で元の環へ戻す。 -/
theorem length_rootStage_koszulHomology (n : ℕ) {r : ℕ} (z : Fin r → D) (i : ℤ) :
    letI := Module.compHom
      ((koszulComplex (perfectionRootStageEquiv D p n ∘ z)).homology i)
      (algebraMap (TowerStage A t p n) (perfectionRootStage D p n))
    Module.length (TowerStage A t p n)
      ((koszulComplex (perfectionRootStageEquiv D p n ∘ z)).homology i) =
        Module.length D ((koszulComplex z).homology i) := by
  let : CharP A p := (algebraMap A D).charP hinj p
  let er := residueFieldEquiv_of_surjective (R := A) D hres
  let : CharP (ResidueField A) p := er.toRingHom.charP er.injective p
  let : PerfectField (ResidueField A) := PerfectField.of_ringEquiv er.symm
  let := isRegularLocalRing_towerStage A t p ht hdim n
  let := isDomain_of_isRegularLocalRing (TowerStage A t p n)
  let := towerStage_free A t p n
  let : CharP (TowerStage A t p n) p :=
    charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective A _) p
  let eA := towerStageFrobeniusEquiv A t p ht n
  let eD := perfectionRootStageEquiv D p n
  let : IsLocalRing (perfectionRootStage D p n) :=
    IsLocalRing.of_surjective' eD.toRingHom eD.surjective
  have he (a : A) : eD (algebraMap A D a) =
      algebraMap (TowerStage A t p n) (perfectionRootStage D p n) (eA.symm a) := by
    have hf : towerStageFrobenius A t p n (eA.symm a) = a := by
      rw [← towerStageFrobeniusEquiv_apply A t p ht n]
      exact eA.apply_symm_apply a
    change perfectionRootStageEquiv D p n (algebraMap A D a) =
      towerStageToRootStage A D p t n (eA.symm a)
    simpa only [hf] using towerStageToRootStage_frobenius A D p t n (eA.symm a)
  have hres' : Function.Surjective
      ((residue (perfectionRootStage D p n)).comp
        (algebraMap (TowerStage A t p n) (perfectionRootStage D p n))) := by
    intro k
    obtain ⟨k', rfl⟩ := (ResidueField.mapEquiv eD).surjective k
    obtain ⟨a, ha⟩ := hres k'
    refine ⟨eA.symm a, ?_⟩
    change residue _ (algebraMap _ _ (eA.symm a)) = _
    rw [← he]
    exact congrArg (ResidueField.mapEquiv eD) ha
  let M := (koszulComplex (eD ∘ z)).homology i
  let : Module (TowerStage A t p n) M :=
    Module.compHom M (algebraMap (TowerStage A t p n) (perfectionRootStage D p n))
  let : IsScalarTower (TowerStage A t p n) (perfectionRootStage D p n) M :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact (length_eq_of_common_residueField hres' M).trans
    (length_homology_koszul_equiv eD z i)

include ht hdim hinj hres in
/-- 通常の包含で根の段に送った列は、元の環では成分ごとの `p^n` 乗に対応する。 -/
theorem length_rootStage_base_koszulHomology (n : ℕ) {r : ℕ} (z : Fin r → D) (i : ℤ) :
    letI := Module.compHom
      ((koszulComplex (perfectionRootStageBaseMap D p n ∘ z)).homology i)
      (algebraMap (TowerStage A t p n) (perfectionRootStage D p n))
    Module.length (TowerStage A t p n)
      ((koszulComplex (perfectionRootStageBaseMap D p n ∘ z)).homology i) =
        Module.length D ((koszulComplex (fun j ↦ z j ^ (p ^ n))).homology i) := by
  have he : perfectionRootStageBaseMap D p n ∘ z =
      perfectionRootStageEquiv D p n ∘ (fun j ↦ z j ^ (p ^ n)) := by
    funext j
    exact (perfectionRootStageEquiv_pow D p n (z j)).symm
  exact (congrArg (fun x : Fin r → perfectionRootStage D p n ↦
    letI := Module.compHom ((koszulComplex x).homology i)
      (algebraMap (TowerStage A t p n) (perfectionRootStage D p n))
    Module.length (TowerStage A t p n) ((koszulComplex x).homology i)) he).trans
      (length_rootStage_koszulHomology A D p t ht hdim hinj hres n _ i)

include ht hdim hinj hres in
/-- パラメータ系の根の段でのホモロジーは、有限段上で有限長である。 -/
theorem isFiniteLength_rootStage_base_koszulHomology [IsNoetherianRing D]
    (n : ℕ) (z : Fin h → D) (hz : IsSystemOfParameters D z) (i : ℤ) :
    letI := Module.compHom
      ((koszulComplex (perfectionRootStageBaseMap D p n ∘ z)).homology i)
      (algebraMap (TowerStage A t p n) (perfectionRootStage D p n))
    IsFiniteLength (TowerStage A t p n)
      ((koszulComplex (perfectionRootStageBaseMap D p n ∘ z)).homology i) := by
  let : Module (TowerStage A t p n)
      ((koszulComplex (perfectionRootStageBaseMap D p n ∘ z)).homology i) :=
    Module.compHom _ (algebraMap (TowerStage A t p n) (perfectionRootStage D p n))
  rw [← Module.length_ne_top_iff,
    length_rootStage_base_koszulHomology A D p t ht hdim hinj hres n z i]
  exact Module.length_ne_top_iff.mpr
    (isFiniteLength_koszulHomology_of_isSystemOfParameters D _
      (hz.pow D _ (pow_pos (Fact.out : p.Prime).pos n)) i)

variable [Algebra A (PerfectClosure D p)]

/-- 元の環から近似部分代数への通常の包含。 -/
noncomputable def perfectionApproximationBaseMap (n : ℕ) :
    D →+* perfectionApproximation D p (Tower A t p) n :=
  (rootStageToApproximation A D p t n).comp (perfectionRootStageBaseMap D p n)

omit [IsRegularLocalRing A] [IsAdicComplete (maximalIdeal A) A] [IsLocalRing D]
  [Algebra A D] [CharP (ResidueField D) p] [PerfectField (ResidueField D)] in
/-- 近似環への包含を perfection まで合成すると、元の標準写像になる。 -/
@[simp] theorem perfectionApproximationBaseMap_coe (n : ℕ) (d : D) :
    (perfectionApproximationBaseMap A D p t n d : PerfectClosure D p) =
      PerfectClosure.of D p d := by
  rw [perfectionApproximationBaseMap, RingHom.comp_apply, rootStageToApproximation_coe,
    perfectionRootStageBaseMap_coe]

variable (hbase : ∀ a : A, algebraMap A (PerfectClosure D p) a =
      PerfectClosure.of D p (algebraMap A D a))
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable)

include ht hdim hinj hres hbase hsep in
/-- パラメータ系について、近似環の Koszul ホモロジーの長さは
`ℓ_D H^i(z^(p^n); D) / p^(nh)` に等しく、塔上で冪ねじれでもある。
有限段の有限長性と必要な平坦性は、元の仮定から証明内で供給する。 -/
theorem perfectionApproximation_koszulHomology_length [IsNoetherianRing D]
    (n : ℕ) (z : Fin h → D) (hz : IsSystemOfParameters D z) (i : ℤ) :
    letI := Module.compHom
      ((koszulComplex (perfectionApproximationBaseMap A D p t n ∘ z)).homology i)
      (algebraMap (Tower A t p) (perfectionApproximation D p (Tower A t p) n))
    towerLengthFun A t p
      ((koszulComplex (perfectionApproximationBaseMap A D p t n ∘ z)).homology i) =
        (Module.length D ((koszulComplex (fun j ↦ z j ^ (p ^ n))).homology i) : ℝ≥0∞) /
          (stageRank h p n : ℝ≥0∞) ∧
    IsPowTorsion (towerMaxIdeal A t p)
      ((koszulComplex (perfectionApproximationBaseMap A D p t n ∘ z)).homology i) := by
  let S := TowerStage A t p n
  let R := Tower A t p
  let T := perfectionRootStage D p n
  let B := perfectionApproximation D p R n
  let : Algebra T B := (rootStageToApproximation A D p t n).toAlgebra
  let : Algebra S B := ((algebraMap R B).comp (algebraMap S R)).toAlgebra
  let : IsScalarTower S R B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower S T B := IsScalarTower.of_algebraMap_eq fun a ↦ by
    apply Subtype.ext
    change towerToPerfect A (PerfectClosure D p) t p (towerOf A t p n a) =
      (rootStageToApproximation A D p t n (towerStageToRootStage A D p t n a) :
        PerfectClosure D p)
    rw [rootStageToApproximation_coe, towerToPerfect_of]
    exact (towerStageToRootStage_coe A D p t hbase n a).symm
  let e := perfectBaseChangeEquiv A D p t hbase ht hdim hinj hres hsep n
  let : Algebra.IsPushout S R T B := ⟨IsBaseChange.of_equiv e.toLinearEquiv (by
    intro d
    exact RingHom.congr_fun
      (perfectBaseChangeEquiv_includeRight A D p t hbase ht hdim hinj hres hsep n) d)⟩
  let x := perfectionRootStageBaseMap D p n ∘ z
  let : Module S ((koszulComplex x).homology i) := Module.compHom _ (algebraMap S T)
  let : Module R ((koszulComplex (algebraMap T B ∘ x)).homology i) :=
    Module.compHom _ (algebraMap R B)
  have hfin := isFiniteLength_rootStage_base_koszulHomology
    A D p t ht hdim hinj hres n z hz i
  have hmem j : t j ∈ maximalIdeal A := ht ▸ Ideal.subset_span (Set.mem_range_self j)
  change towerLengthFun A t p ((koszulComplex (algebraMap T B ∘ x)).homology i) = _ ∧ _
  refine ⟨?_, isPowTorsion_koszulHomology_of_baseChange A t p hmem n T B x i hfin⟩
  rw [towerLengthFun_koszulHomology_of_baseChange A t p hmem n T B x i hfin]
  rw [length_rootStage_base_koszulHomology A D p t ht hdim hinj hres n z i]

include hinj hbase in
omit [IsAdicComplete (maximalIdeal A) A] [CharP (ResidueField D) p]
  [PerfectField (ResidueField D)] in
set_option backward.isDefEq.respectTransparency false in
/-- 一つのパラメータ系を固定すると、全ての近似段・全ての次数のホモロジーを
`m_A Λ` の同じ冪で消せる。段ごとの有限長性から冪を選び直す必要はない。 -/
theorem exists_uniform_pow_torsion_perfectionApproximation_koszul
    [IsNoetherianRing D] [Module.Finite A D]
    (z : Fin h → D) (hz : IsSystemOfParameters D z) :
    ∃ N : ℕ, ∀ (n : ℕ) (i : ℤ),
      letI := Module.compHom
        ((koszulComplex (perfectionApproximationBaseMap A D p t n ∘ z)).homology i)
        (algebraMap (Tower A t p) (perfectionApproximation D p (Tower A t p) n))
      Module.IsTorsionBySet (Tower A t p)
        ((koszulComplex (perfectionApproximationBaseMap A D p t n ∘ z)).homology i)
        ((towerMaxIdeal A t p) ^ N : Ideal (Tower A t p)) := by
  obtain ⟨N, hN⟩ := exists_pow_annihilates_koszul_baseChange D z hz
  refine ⟨N, fun n i ↦ ?_⟩
  let R := Tower A t p
  let B := perfectionApproximation D p R n
  let φ := perfectionApproximationBaseMap A D p t n
  let : Algebra D B := φ.toAlgebra
  let : Algebra A B := ((algebraMap R B).comp (algebraMap A R)).toAlgebra
  let : IsScalarTower A R B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower A D B := IsScalarTower.of_algebraMap_eq fun a ↦ by
    apply Subtype.ext
    change towerToPerfect A (PerfectClosure D p) t p (algebraMap A R a) =
      (perfectionApproximationBaseMap A D p t n (algebraMap A D a) : PerfectClosure D p)
    rw [(towerToPerfect A (PerfectClosure D p) t p).commutes,
      perfectionApproximationBaseMap_coe, hbase]
  let M := (koszulComplex (φ ∘ z)).homology i
  let : Module R M := Module.compHom M (algebraMap R B)
  have hle := pow_le_pow_left' (towerMaxIdeal_map_le A D hinj t p B) N
  have hann : ((towerMaxIdeal A t p) ^ N).map (algebraMap R B) ≤
      Module.annihilator B M := by
    rw [Ideal.map_pow]
    apply hle.trans
    change (maximalIdeal D).map φ ^ N ≤
      Module.annihilator B ((koszulComplex (φ ∘ z)).homology i)
    simpa only [Ideal.map_pow] using hN B φ i
  rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe]
  intro a ha
  rw [Module.mem_annihilator]
  exact Module.mem_annihilator.mp (hann (Ideal.mem_map_of_mem _ ha))

end SerrePositivity.Section2
