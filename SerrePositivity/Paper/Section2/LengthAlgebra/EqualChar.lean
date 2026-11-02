module

public import SerrePositivity.CommutativeAlgebra.RootTower.PerfectConductor
public import SerrePositivity.CommutativeAlgebra.Perfection.Approximation
public import SerrePositivity.LengthAlgebra.Normalized
public import SerrePositivity.LengthAlgebra.RootTowerLength.Tower
public import SerrePositivity.CommutativeAlgebra.Length.QuotientPower
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Order.MonotoneConvergence
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Existence
public import SerrePositivity.CommutativeAlgebra.KoszulMultiplicity.Formula
public import SerrePositivity.HomologicalAlgebra.KoszulOrdinaryLength
public import SerrePositivity.CommutativeAlgebra.Koszul.FiniteLength
public import SerrePositivity.HomologicalAlgebra.KoszulDirectedUnion
public import SerrePositivity.CommutativeAlgebra.FrobeniusKoszulLimit

/-! # 等標数の長さ代数（perfection）

## 概要

正則な基底 `A` 上の有限拡大 `D`（標数 `p`）で、perfection 全体に共通の非零分母を作り（`PerfectConductor`）、近似環の核を分母倍の余核の長さで評価し、近似環の商の正規化長さを有限段の長さ `/p^(nh)` で表す。通常の Frobenius 商の正規化長さが perfection の商の正規化長さへ収束すること、近似環の Koszul ホモロジーの長さを `ℓ_D H^i(z^(p^n); D)/p^(nh)` と同定し、全段で一様な消去冪を与えること、高次の正規化長さが零へ収束するという前提から perfection の Koszul ホモロジーの消滅と商の長さの重複度との同定を導く。

## 方針

有向極限とホモロジーの可換性で近似環から perfection へ移し、任意の両立する塔作用は標準作用と一致することで `towerLengthOn` へ移す。

## 規約

高次の消滅極限はここでは仮定で、供給は `LengthAlgebra` が行う。長さの公式は Lemma 2.3 (b) の入力 (C1) を使う（証明済み）。

## 使われ方

`Paper/Section2/LengthAlgebra`。
-/

@[expose] public noncomputable section

universe u

section PerfectConductorPart

namespace SerrePositivity.Section2

variable (D : Type u) [CommRing D] (p : ℕ) [Fact p.Prime] [CharP D p]

attribute [local instance] towerPerfectionAlgebra

/-- 論文の等標数の設定から、perfection 全体に共通の非零分母を構成する。
正則基底の正規性と剰余体の完全性を証明内で供給し、追加の仮定にはしない。
基底の正規性は証明済みの正則パラメータから導かれる。 -/
theorem exists_tower_perfection_conductor
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsDomain D] [IsLocalRing D] [Algebra A D] [Module.Finite A D]
    [Algebra A (PerfectClosure D p)]
    [CharP (IsLocalRing.ResidueField D) p] [PerfectField (IsLocalRing.ResidueField D)]
    {h : ℕ} (t : Fin h → A)
    (ht : Ideal.span (Set.range t) = IsLocalRing.maximalIdeal A)
    (hdim : ringKrullDim A = h) (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((IsLocalRing.residue D).comp (algebraMap A D)))
    (hbase : ∀ a : A, algebraMap A (PerfectClosure D p) a =
      PerfectClosure.of D p (algebraMap A D a))
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable) :
    ∃ g : A, g ≠ 0 ∧ ∀ c : PerfectClosure D p,
      PerfectClosure.of D p (algebraMap A D g) * c ∈
        perfectionApproximation D p (Tower A t p) 0 := by
  let := isIntegrallyClosed_of_isRegularLocalRing A
  let er := residueFieldEquiv_of_surjective (R := A) D hres
  let : CharP (IsLocalRing.ResidueField A) p := er.toRingHom.charP er.injective p
  let : PerfectField (IsLocalRing.ResidueField A) := PerfectField.of_ringEquiv er.symm
  exact exists_tower_perfection_conductor_of_normal_base D p A t ht hdim hinj hbase hsep

end SerrePositivity.Section2

end PerfectConductorPart

section PerfectApproximationPart

namespace SerrePositivity.Section2

variable (D : Type u) [CommRing D] (p : ℕ) [Fact p.Prime] [CharP D p]
    (R : Type u) [CommRing R] [Algebra R (PerfectClosure D p)]

/-- 有限段の近似に対する、共通分母からの核の評価。
長さの有限性と共通分母の条件を明示的に受け取る。この二条件を定理2.5の設定で
得るためには、それぞれテンソル積表示とトレースの議論が別途必要である。 -/
theorem perfectionApproximation_kernel_bound {J : Ideal R} (lam : NormalizedLength R J)
    (n : ℕ) (I : Ideal (perfectionApproximation D p R n))
    (g : perfectionApproximation D p R n)
    (hg : ∀ c : PerfectClosure D p, (g : PerfectClosure D p) * c ∈
      perfectionApproximation D p R n)
    (htors : IsPowTorsion J ((perfectionApproximation D p R n) ⧸ I))
    (hfinite : lam.len ((perfectionApproximation D p R n) ⧸ I) ≠ ⊤) :
    lam.len (LinearMap.ker
      ((quotientToExtension (C := PerfectClosure D p) I).toLinearMap.restrictScalars R)) ≤
    lam.len ((perfectionApproximation D p R n) ⧸ (I ⊔ Ideal.span {g})) := by
  apply len_ker_quotientToExtension_le R lam Subtype.val_injective I g _ htors hfinite
  intro c
  exact ⟨⟨(g : PerfectClosure D p) * c, hg c⟩, rfl⟩

end SerrePositivity.Section2

end PerfectApproximationPart

section PerfectApproximationLengthPart

open scoped TensorProduct ENNReal
open IsLocalRing
namespace SerrePositivity.Section2

/-- 有限段から係数拡大された代数の商の長さ。
係数拡大と商を交換し、有限段の長さの公式を適用する。 -/
theorem towerLengthFun_quotient_of_baseChange
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A) (n : ℕ)
    (T B : Type u) [CommRing T] [CommRing B]
    [Algebra (TowerStage A t p n) T] [Algebra (Tower A t p) B]
    (e : Tower A t p ⊗[TowerStage A t p n] T ≃ₐ[Tower A t p] B)
    (I : Ideal T) (hI : IsFiniteLength (TowerStage A t p n) (T ⧸ I)) :
    towerLengthFun A t p
      (B ⧸ I.map (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) =
      (Module.length (TowerStage A t p n) (T ⧸ I) : ℝ≥0∞) /
        (stageRank h p n : ℝ≥0∞) := by
  rw [← towerLengthFun_congr (baseChangeIdealQuotientEquiv
    (TowerStage A t p n) (Tower A t p) T B e I).toLinearEquiv]
  exact towerLengthFun_tensor_of_finiteLength A t p ht n (T ⧸ I) hI

/-- 有限段の有限長な商から係数拡大で得た商は、塔の極大イデアルの像の冪で消える。
商と係数拡大の交換同型を使うので、近似環の有限性を別に仮定しない。 -/
theorem isPowTorsion_quotient_of_baseChange
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A) (n : ℕ)
    (T B : Type u) [CommRing T] [CommRing B]
    [Algebra (TowerStage A t p n) T] [Algebra (Tower A t p) B]
    (e : Tower A t p ⊗[TowerStage A t p n] T ≃ₐ[Tower A t p] B)
    (I : Ideal T) (hI : IsFiniteLength (TowerStage A t p n) (T ⧸ I)) :
    IsPowTorsion (towerMaxIdeal A t p)
      (B ⧸ I.map (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) := by
  let := isLocalRing_towerStage A t p ht n
  apply IsPowTorsion.of_equiv (baseChangeIdealQuotientEquiv
    (TowerStage A t p n) (Tower A t p) T B e I).toLinearEquiv
  apply isPowTorsion_tower_tensor
  obtain ⟨k, hk⟩ := IsFiniteLength.exists_isTorsionBySet_maximalIdeal_pow hI
  refine ⟨k, ?_⟩
  rw [Module.isTorsionBySet_iff_subset_annihilator] at hk ⊢
  exact (pow_le_pow_left'
    (le_of_isMaximal_towerStage A t p ht n (maximalIdeal (TowerStage A t p n))).1 k).trans hk

section QuotientImages
attribute [local instance] towerPerfectionAlgebra

variable (A D : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing D]
    (p : ℕ) [Fact p.Prime] [CharP D p] {h : ℕ} (t : Fin h → A)
    (htm : ∀ i, t i ∈ maximalIdeal A)
    [Algebra A (PerfectClosure D p)]

include htm

/-- 冪ねじれな perfection の商の長さは、近似部分代数から来る像の長さの上限。
像の増大・被覆と、既存の正規化長さの上限性を組み合わせる。 -/
theorem towerLengthFun_quotient_eq_iSup_image (J : Ideal (PerfectClosure D p))
    (hJ : IsPowTorsion (towerMaxIdeal A t p) ((PerfectClosure D p) ⧸ J)) :
    towerLengthFun A t p ((PerfectClosure D p) ⧸ J) =
      ⨆ n, towerLengthFun A t p (perfectionQuotientImage D p (Tower A t p) J n) := by
  have he := NormalizedLength.len_iSup_of_directed (towerLength_hasSup A t p htm) hJ
    (perfectionQuotientImage D p (Tower A t p) J)
    (perfectionQuotientImage_monotone D p (Tower A t p) J).directed_le
  rw [iSup_perfectionQuotientImage] at he
  exact (towerLengthFun_congr (A := A) (t := t) (p := p) Submodule.topEquiv).symm.trans he

/-- 近似部分代数から来る像の長さは単調に増大し、perfection の商の長さに収束する。
商全体の長さが無限大の場合も含む。 -/
theorem towerLengthFun_quotientImage_tendsto (J : Ideal (PerfectClosure D p))
    (hJ : IsPowTorsion (towerMaxIdeal A t p) ((PerfectClosure D p) ⧸ J)) :
    Filter.Tendsto (fun n ↦ towerLengthFun A t p
      (perfectionQuotientImage D p (Tower A t p) J n)) Filter.atTop
        (nhds (towerLengthFun A t p ((PerfectClosure D p) ⧸ J))) := by
  rw [towerLengthFun_quotient_eq_iSup_image A D p t htm J hJ]
  apply tendsto_atTop_iSup
  intro n m hnm
  exact (towerLength A t p htm).len_le_of_injective
    (Submodule.inclusion (perfectionQuotientImage_monotone D p (Tower A t p) J hnm))
    (Submodule.inclusion_injective _) (hJ.submodule _)

end QuotientImages

section Perfection

attribute [local instance] rootStageAlgebra towerPerfectionAlgebra stagePerfectionAlgebra
  stageTowerPerfection

variable (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing D] [IsDomain D] [IsLocalRing D] [Algebra A D]
    (p : ℕ) [Fact p.Prime] [CharP D p]
    [CharP (ResidueField D) p] [PerfectField (ResidueField D)]
    {h : ℕ} (t : Fin h → A) [Algebra A (PerfectClosure D p)]
    (hbase : ∀ a : A, algebraMap A (PerfectClosure D p) a =
      PerfectClosure.of D p (algebraMap A D a))
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (hdim : ringKrullDim A = h)
    (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable)

include ht hdim hinj hres in
omit [Algebra A (PerfectClosure D p)] in
/-- 根の段の商を有限段上で測った長さは、Frobenius 同型で戻した `D` 上の長さに等しい。
係数環と代数の同型の可換性、および `A → D` の剰余体の一致を使う。
分離性の仮定はこの比較には不要である。 -/
theorem length_rootStage_quotient (n : ℕ) (J : Ideal D) :
    Module.length (TowerStage A t p n)
      ((perfectionRootStage D p n) ⧸ J.map (perfectionRootStageEquiv D p n).toRingHom) =
      Module.length D (D ⧸ J) := by
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
  have he : ∀ a : A, perfectionRootStageEquiv D p n (algebraMap A D a) =
      algebraMap (TowerStage A t p n) (perfectionRootStage D p n) (eA.symm a) := by
    intro a
    have hf : towerStageFrobenius A t p n (eA.symm a) = a := by
      rw [← towerStageFrobeniusEquiv_apply A t p ht n]
      exact eA.apply_symm_apply a
    change perfectionRootStageEquiv D p n (algebraMap A D a) =
      towerStageToRootStage A D p t n (eA.symm a)
    simpa only [hf] using towerStageToRootStage_frobenius A D p t n (eA.symm a)
  exact (length_quotient_eq_of_equiv D (perfectionRootStage D p n)
    eA.symm (perfectionRootStageEquiv D p n) he J).symm.trans
    (length_eq_of_common_residueField hres (D ⧸ J))

/-- 近似環の同型は、テンソル積の右因子の包含を根の段の自然な包含に送る。 -/
theorem perfectBaseChangeEquiv_includeRight (n : ℕ) :
    (perfectBaseChangeEquiv A D p t hbase ht hdim hinj hres hsep n).toRingHom.comp
      Algebra.TensorProduct.includeRight.toRingHom = rootStageToApproximation A D p t n := by
  apply RingHom.ext
  intro d
  apply Subtype.ext
  change (perfectBaseChangeEquiv A D p t hbase ht hdim hinj hres hsep n
    (1 ⊗ₜ[TowerStage A t p n] d) : PerfectClosure D p) = _
  rw [perfectBaseChangeEquiv_coe, perfectBaseChangeMap_tmul, map_one, one_mul]
  exact (rootStageToApproximation_coe A D p t n d).symm

include hbase ht hdim hinj hres hsep in
/-- 根の段のイデアル `I` を近似環に拡大した商の正規化長さ。
段の商が有限長なら、その通常の長さを `p^(nh)` で割ればよい。 -/
theorem towerLengthFun_perfectionApproximation_quotient (n : ℕ)
    (I : Ideal (perfectionRootStage D p n))
    (hI : IsFiniteLength (TowerStage A t p n) ((perfectionRootStage D p n) ⧸ I)) :
    towerLengthFun A t p
      ((perfectionApproximation D p (Tower A t p) n) ⧸
        I.map (rootStageToApproximation A D p t n)) =
      (Module.length (TowerStage A t p n) ((perfectionRootStage D p n) ⧸ I) : ℝ≥0∞) /
        (stageRank h p n : ℝ≥0∞) := by
  rw [← perfectBaseChangeEquiv_includeRight A D p t hbase ht hdim hinj hres hsep n]
  exact towerLengthFun_quotient_of_baseChange A t p
    (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) n _ _ _ I hI

include hbase ht hdim hinj hres hsep in
/-- 近似環の商の冪ねじれ条件は、根の有限段での有限長性から従う。 -/
theorem isPowTorsion_perfectionApproximation_quotient (n : ℕ)
    (I : Ideal (perfectionRootStage D p n))
    (hI : IsFiniteLength (TowerStage A t p n) ((perfectionRootStage D p n) ⧸ I)) :
    IsPowTorsion (towerMaxIdeal A t p)
      ((perfectionApproximation D p (Tower A t p) n) ⧸
        I.map (rootStageToApproximation A D p t n)) := by
  rw [← perfectBaseChangeEquiv_includeRight A D p t hbase ht hdim hinj hres hsep n]
  exact isPowTorsion_quotient_of_baseChange A t p
    (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) n _ _ _ I hI

include hbase ht hdim hinj hres hsep in
/-- 共通分母による核の評価を、有限段から来る近似環の商へ適用する。
冪ねじれと正規化長さの有限性は、有限段での有限長性から証明する。 -/
theorem towerLengthFun_perfectionApproximation_kernel_le (n : ℕ)
    (I : Ideal (perfectionRootStage D p n))
    (hI : IsFiniteLength (TowerStage A t p n) ((perfectionRootStage D p n) ⧸ I))
    (g : D) (hg : ∀ c : PerfectClosure D p, perfectionRootHom D p n g * c ∈
      perfectionApproximation D p (Tower A t p) n) :
    towerLengthFun A t p (LinearMap.ker
      ((quotientToExtension (C := PerfectClosure D p)
        (I.map (rootStageToApproximation A D p t n))).toLinearMap.restrictScalars
          (Tower A t p))) ≤
      towerLengthFun A t p ((perfectionApproximation D p (Tower A t p) n) ⧸
        (I ⊔ Ideal.span {perfectionRootStageEquiv D p n g}).map
          (rootStageToApproximation A D p t n)) := by
  have hfinite : towerLengthFun A t p ((perfectionApproximation D p (Tower A t p) n) ⧸
      I.map (rootStageToApproximation A D p t n)) ≠ ⊤ := by
    rw [towerLengthFun_perfectionApproximation_quotient A D p t hbase ht hdim hinj hres hsep n I hI]
    apply ENNReal.div_ne_top (ENat.toENNReal_ne_top.mpr (Module.length_ne_top_iff.mpr hI))
    exact_mod_cast pow_ne_zero (n * h) (Fact.out : p.Prime).ne_zero
  have hb := perfectionApproximation_kernel_bound D p (Tower A t p)
    (towerLength A t p (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)))
    n (I.map (rootStageToApproximation A D p t n))
    (rootStageToApproximation A D p t n (perfectionRootStageEquiv D p n g))
    (by simpa only [rootStageToApproximation_coe, perfectionRootStageEquiv_coe] using hg)
    (isPowTorsion_perfectionApproximation_quotient A D p t hbase ht hdim hinj hres hsep n I hI)
    hfinite
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  exact hb

include ht hdim hinj hres in
omit [Algebra A (PerfectClosure D p)] in
/-- 通常の包含で作った根の段の商の長さを、元の環の Frobenius 冪の商へ戻す。 -/
theorem length_rootStage_base_quotient (n : ℕ) (H : Ideal D) :
    Module.length (TowerStage A t p n)
      ((perfectionRootStage D p n) ⧸ H.map (perfectionRootStageBaseMap D p n)) =
      Module.length D (D ⧸ H.map (iterateFrobenius D p n)) := by
  have hf : (perfectionRootStageEquiv D p n).toRingHom.comp (iterateFrobenius D p n) =
      perfectionRootStageBaseMap D p n := by
    apply RingHom.ext
    intro x
    exact perfectionRootStageEquiv_pow D p n x
  rw [← hf, ← Ideal.map_map, length_rootStage_quotient A D p t ht hdim hinj hres n]

include ht hdim hinj hres in
omit [Algebra A (PerfectClosure D p)] in
/-- 元の有限長な商の Frobenius 冪を根の段へ移すと、有限段上でも有限長。
Noether 性を使うのは Frobenius 冪による有限長性の保存だけである。 -/
theorem isFiniteLength_rootStage_base_quotient [IsNoetherianRing D]
    (n : ℕ) (H : Ideal D) (hH : IsFiniteLength D (D ⧸ H)) :
    IsFiniteLength (TowerStage A t p n)
      ((perfectionRootStage D p n) ⧸ H.map (perfectionRootStageBaseMap D p n)) := by
  rw [← Module.length_ne_top_iff, length_rootStage_base_quotient A D p t ht hdim hinj hres]
  exact Module.length_ne_top_iff.mpr (isFiniteLength_quotient_map_iterateFrobenius D H hH p n)

include hbase ht hdim hinj hres hsep in
/-- 元の環の商が有限長なら、perfection での拡大イデアルによる商は塔上で冪ねじれ。
初段の商の冪ねじれを環拡大で移し、拡大イデアルの同定を使う。 -/
theorem isPowTorsion_perfection_quotient [IsNoetherianRing D]
    (H : Ideal D) (hH : IsFiniteLength D (D ⧸ H)) :
    IsPowTorsion (towerMaxIdeal A t p)
      ((PerfectClosure D p) ⧸ H.map (PerfectClosure.of D p)) := by
  have hI := isFiniteLength_rootStage_base_quotient A D p t ht hdim hinj hres 0 H hH
  have hs := isPowTorsion_quotient_extension (C := PerfectClosure D p) (Tower A t p)
    (towerMaxIdeal A t p)
    ((H.map (perfectionRootStageBaseMap D p 0)).map (rootStageToApproximation A D p t 0))
    (isPowTorsion_perfectionApproximation_quotient A D p t hbase ht hdim hinj hres hsep 0 _ hI)
  rwa [rootStageToApproximation_map_extension] at hs

include hbase ht hdim hinj hres hsep in
/-- `D/H` が有限長なら、近似段の像の正規化長さは `C/HC` の正規化長さへ収束する。
商全体の冪ねじれはここで導き、追加仮定にはしない。 -/
theorem towerLengthFun_perfection_quotientImage_tendsto [IsNoetherianRing D]
    (H : Ideal D) (hH : IsFiniteLength D (D ⧸ H)) :
    Filter.Tendsto (fun n ↦ towerLengthFun A t p
      (perfectionQuotientImage D p (Tower A t p) (H.map (PerfectClosure.of D p)) n))
      Filter.atTop (nhds (towerLengthFun A t p
        ((PerfectClosure D p) ⧸ H.map (PerfectClosure.of D p)))) :=
  towerLengthFun_quotientImage_tendsto A D p t
    (fun i ↦ by rw [← ht]; exact Ideal.subset_span (Set.mem_range_self i)) _
    (isPowTorsion_perfection_quotient A D p t hbase ht hdim hinj hres hsep H hH)

omit [IsRegularLocalRing A] [IsAdicComplete (maximalIdeal A) A]
  [IsLocalRing D] [Algebra A D] [CharP (ResidueField D) p] [PerfectField (ResidueField D)] in
/-- 段ごとの商写像の像の長さは、固定した商 `C/HC` の部分加群として定義した像の長さに等しい。
拡大イデアルの等式に沿って商を同定し、元の商への全射を使って像を比較する。 -/
theorem towerLengthFun_perfectionApproximation_range_eq_image (n : ℕ) (H : Ideal D) :
    towerLengthFun A t p (LinearMap.range
      ((quotientToExtension (C := PerfectClosure D p)
        ((H.map (perfectionRootStageBaseMap D p n)).map
          (rootStageToApproximation A D p t n))).toLinearMap.restrictScalars (Tower A t p))) =
      towerLengthFun A t p
        (perfectionQuotientImage D p (Tower A t p) (H.map (PerfectClosure.of D p)) n) := by
  let C := PerfectClosure D p
  let B := perfectionApproximation D p (Tower A t p) n
  let I := (H.map (perfectionRootStageBaseMap D p n)).map (rootStageToApproximation A D p t n)
  let J := H.map (PerfectClosure.of D p)
  let f := (quotientToExtension (C := C) I).toLinearMap.restrictScalars (Tower A t p)
  have he : I.map (algebraMap B C) = J := rootStageToApproximation_map_extension A D p t n H
  let e := (Submodule.quotEquivOfEq _ _ he).restrictScalars (Tower A t p)
  have he_apply (b : B) : e (f (Ideal.Quotient.mk I b)) = Ideal.Quotient.mk J (b : C) := by
    dsimp [e, f]
    rw [quotientToExtension_mk, LinearEquiv.restrictScalars_apply]
    change Submodule.quotEquivOfEq _ _ he
      (Submodule.Quotient.mk (algebraMap B C b)) = _
    rw [Submodule.quotEquivOfEq_mk]
    simp only [Subalgebra.algebraMap_eq]
    rfl
  have hm : (LinearMap.range f).map e.toLinearMap =
      perfectionQuotientImage D p (Tower A t p) J n := by
    ext x
    constructor
    · rintro ⟨y, ⟨b, rfl⟩, rfl⟩
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      exact Submodule.mem_map.mpr ⟨(b : C), b.property, (he_apply b).symm⟩
    · rintro ⟨c, hc, rfl⟩
      refine Submodule.mem_map.mpr ⟨f (Ideal.Quotient.mk I ⟨c, hc⟩), ⟨_, rfl⟩, ?_⟩
      exact he_apply ⟨c, hc⟩
  have hh := towerLengthFun_congr (A := A) (t := t) (p := p)
    (Submodule.equivMapOfInjective e.toLinearMap e.injective (LinearMap.range f))
  rw [hm] at hh
  exact hh

include hbase ht hdim hinj hres hsep in
/-- 近似環の商から perfection の商への写像について、核と像の正規化長さの和は
元の環の Frobenius 商の長さを `q^h` で割った値に等しい。
後に核の消滅と Hilbert–Kunz 極限を合わせるための、各段での正確な等式である。 -/
theorem towerLengthFun_perfectionApproximation_kernel_add_range [IsNoetherianRing D]
    (n : ℕ) (H : Ideal D) (hH : IsFiniteLength D (D ⧸ H)) :
    let f := (quotientToExtension (C := PerfectClosure D p)
      ((H.map (perfectionRootStageBaseMap D p n)).map
        (rootStageToApproximation A D p t n))).toLinearMap.restrictScalars (Tower A t p)
    towerLengthFun A t p (LinearMap.ker f) + towerLengthFun A t p (LinearMap.range f) =
      (Module.length D (D ⧸ H.map (iterateFrobenius D p n)) : ℝ≥0∞) /
        (stageRank h p n : ℝ≥0∞) := by
  intro f
  have hI := isFiniteLength_rootStage_base_quotient A D p t ht hdim hinj hres n H hH
  have hs := (towerLength A t p
    (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len_eq_add_ker_range f
    (isPowTorsion_perfectionApproximation_quotient A D p t hbase ht hdim hinj hres hsep n _ hI)
  rw [towerLength_len, towerLength_len, towerLength_len] at hs
  rw [← hs, towerLengthFun_perfectionApproximation_quotient
    A D p t hbase ht hdim hinj hres hsep n _ hI,
    length_rootStage_base_quotient A D p t ht hdim hinj hres]

include hbase ht hdim hinj hres hsep in
/-- 元の環の有限長な商を根の同型で近似環へ移したときの正規化長さ。
有限長性の仮定も長さの値も、元の環 `D` の商だけで記述できる。 -/
theorem towerLengthFun_perfectionApproximation_quotient_of_finiteLength (n : ℕ)
    (J : Ideal D) (hJ : IsFiniteLength D (D ⧸ J)) :
    towerLengthFun A t p
      ((perfectionApproximation D p (Tower A t p) n) ⧸
        (J.map (perfectionRootStageEquiv D p n).toRingHom).map
          (rootStageToApproximation A D p t n)) =
      (Module.length D (D ⧸ J) : ℝ≥0∞) / (stageRank h p n : ℝ≥0∞) := by
  have he := length_rootStage_quotient A D p t ht hdim hinj hres n J
  have hI : IsFiniteLength (TowerStage A t p n)
      ((perfectionRootStage D p n) ⧸ J.map (perfectionRootStageEquiv D p n).toRingHom) := by
    rw [← Module.length_ne_top_iff, he]
    exact Module.length_ne_top_iff.mpr hJ
  rw [towerLengthFun_perfectionApproximation_quotient A D p t hbase ht hdim hinj hres hsep n _ hI,
    he]

include hbase ht hdim hinj hres hsep in
/-- 論文で用いる `B_q / (H B_q + g^{1/q} B_q)` の長さ公式。
右辺は `D / (H^[q] + (g))` の通常の長さを `q^h` で割ったもの。
この商の有限長性を仮定し、共通分母の存在や漸近評価とは独立に証明する。 -/
theorem towerLengthFun_perfectionApproximation_frobenius_quotient (n : ℕ)
    (H : Ideal D) (g : D)
    (hH : IsFiniteLength D (D ⧸ (H.map (iterateFrobenius D p n) ⊔ Ideal.span {g}))) :
    towerLengthFun A t p
      ((perfectionApproximation D p (Tower A t p) n) ⧸
        (H.map (perfectionRootStageBaseMap D p n) ⊔
          Ideal.span {perfectionRootStageEquiv D p n g}).map
            (rootStageToApproximation A D p t n)) =
      (Module.length D (D ⧸ (H.map (iterateFrobenius D p n) ⊔ Ideal.span {g})) : ℝ≥0∞) /
        (stageRank h p n : ℝ≥0∞) := by
  have hf : (perfectionRootStageEquiv D p n).toRingHom.comp (iterateFrobenius D p n) =
      perfectionRootStageBaseMap D p n := by
    apply RingHom.ext
    intro x
    exact perfectionRootStageEquiv_pow D p n x
  have hm : (H.map (iterateFrobenius D p n) ⊔ Ideal.span {g}).map
      (perfectionRootStageEquiv D p n).toRingHom =
      H.map (perfectionRootStageBaseMap D p n) ⊔
        Ideal.span {perfectionRootStageEquiv D p n g} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_map, hf]
    rfl
  rw [← hm]
  exact towerLengthFun_perfectionApproximation_quotient_of_finiteLength
      A D p t hbase ht hdim hinj hres hsep n _ hH

include hbase ht hdim hinj hres hsep in
/-- 共通分母で割った近似環の商の正規化長さを、多項式的な上界で抑える。
`H` 内の `r` 個の元 `z` が `g` と合わせて有限長の商を定めればよい。
各 Frobenius 段の有限長性もその仮定から導く。
`r < h` の場合、この上界が零へ収束することが誤差消滅の根拠となる。 -/
theorem towerLengthFun_perfectionApproximation_frobenius_quotient_le (n : ℕ)
    (H : Ideal D) (g : D) {r : ℕ} (z : Fin r → D) (hz : ∀ i, z i ∈ H)
    (hfin : IsFiniteLength D (D ⧸ (Ideal.span {g} ⊔ Ideal.span (Set.range z)))) :
    towerLengthFun A t p
      ((perfectionApproximation D p (Tower A t p) n) ⧸
        (H.map (perfectionRootStageBaseMap D p n) ⊔
          Ideal.span {perfectionRootStageEquiv D p n g}).map
            (rootStageToApproximation A D p t n)) ≤
      ((p ^ n : ℕ) : ℝ≥0∞) ^ r *
        (Module.length D (D ⧸ (Ideal.span {g} ⊔ Ideal.span (Set.range z))) : ℝ≥0∞) /
          (stageRank h p n : ℝ≥0∞) := by
  rw [towerLengthFun_perfectionApproximation_frobenius_quotient
    A D p t hbase ht hdim hinj hres hsep n H g
    (isFiniteLength_quotient_frobenius_sup D (Ideal.span {g}) H z hz hfin p n)]
  apply ENNReal.div_le_div_right
  have hb := ENat.toENNReal_mono
    (length_quotient_frobenius_sup_le D (Ideal.span {g}) H z hz p n)
  simpa only [ENat.toENNReal_mul, ENat.toENNReal_pow, ENat.toENNReal_coe] using hb

include hbase ht hdim hinj hres hsep in
/-- 分母 `g` と `h-1` 個の元が有限長の商を定めるなら、分母の根を加えた
近似環の商の正規化長さは零へ収束する。
通常の長さは高々 `q^(h-1)` 倍なので、`q^h` で割ると定数倍の `1/q` で抑えられる。
この補題は元の組の存在を仮定し、その選択に必要な次元論とは独立である。 -/
theorem towerLengthFun_perfectionApproximation_frobenius_quotient_tendsto_zero
    (H : Ideal D) (g : D) {r : ℕ} (hr : r + 1 = h)
    (z : Fin r → D) (hz : ∀ i, z i ∈ H)
    (hfin : IsFiniteLength D (D ⧸ (Ideal.span {g} ⊔ Ideal.span (Set.range z)))) :
    Filter.Tendsto (fun n : ℕ ↦ towerLengthFun A t p
      ((perfectionApproximation D p (Tower A t p) n) ⧸
        (H.map (perfectionRootStageBaseMap D p n) ⊔
          Ideal.span {perfectionRootStageEquiv D p n g}).map
            (rootStageToApproximation A D p t n))) Filter.atTop (nhds 0) := by
  let L : ℝ≥0∞ := Module.length D (D ⧸ (Ideal.span {g} ⊔ Ideal.span (Set.range z)))
  have hL : L ≠ ⊤ := ENat.toENNReal_ne_top.mpr (Module.length_ne_top_iff.mpr hfin)
  have hlim : Filter.Tendsto (fun n : ℕ ↦ L / (p ^ n : ℕ)) Filter.atTop (nhds 0) := by
    have htend := ENNReal.tendsto_nat_nhds_top.comp
      (tendsto_pow_atTop_atTop_of_one_lt (Fact.out : p.Prime).one_lt)
    simpa only [ENNReal.div_top, Function.comp_apply] using
      ENNReal.Tendsto.const_div (a := L) htend (Or.inr hL)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ zero_le) (fun n ↦ ?_)
  have hb := towerLengthFun_perfectionApproximation_frobenius_quotient_le
    A D p t hbase ht hdim hinj hres hsep n H g z hz hfin
  have he : ((p ^ n : ℕ) : ℝ≥0∞) ^ r * L / (stageRank h p n : ℝ≥0∞) =
      L / (p ^ n : ℕ) := by
    have hq : ((p ^ n : ℕ) : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast pow_ne_zero n (Fact.out : p.Prime).ne_zero
    have hqt : ((p ^ n : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    rw [stageRank, ← hr, pow_mul, Nat.cast_pow, pow_succ]
    simpa only [Nat.cast_pow, Nat.cast_mul] using
      ENNReal.mul_div_mul_left L ((p ^ n : ℕ) : ℝ≥0∞)
        (pow_ne_zero r hq) (ENNReal.pow_ne_top hqt)
  exact hb.trans_eq he

include hbase ht hdim hinj hres hsep in
/-- 初段の共通分母と余次元一の有限長な商があれば、近似環の商から perfection の
商への写像の核の正規化長さは零へ収束する。
各段の有限長性・冪ねじれと分母の根による包含は証明内で導く。
この結論を余極限での長さの比較へ渡すことができる。 -/
theorem towerLengthFun_perfectionApproximation_kernel_tendsto_zero [IsNoetherianRing D]
    (H : Ideal D) (hH : IsFiniteLength D (D ⧸ H))
    (g : D) (hg : ∀ c : PerfectClosure D p, PerfectClosure.of D p g * c ∈
      perfectionApproximation D p (Tower A t p) 0)
    {r : ℕ} (hr : r + 1 = h) (z : Fin r → D) (hz : ∀ i, z i ∈ H)
    (hfin : IsFiniteLength D (D ⧸ (Ideal.span {g} ⊔ Ideal.span (Set.range z)))) :
    Filter.Tendsto (fun n : ℕ ↦ towerLengthFun A t p (LinearMap.ker
      ((quotientToExtension (C := PerfectClosure D p)
        ((H.map (perfectionRootStageBaseMap D p n)).map
          (rootStageToApproximation A D p t n))).toLinearMap.restrictScalars
            (Tower A t p)))) Filter.atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (towerLengthFun_perfectionApproximation_frobenius_quotient_tendsto_zero
      A D p t hbase ht hdim hinj hres hsep H g hr z hz hfin)
    (fun _ ↦ zero_le) (fun n ↦ ?_)
  exact towerLengthFun_perfectionApproximation_kernel_le A D p t hbase ht hdim hinj hres hsep
    n _ (isFiniteLength_rootStage_base_quotient A D p t ht hdim hinj hres n H hH)
    g (tower_perfectionApproximation_conductor_root D p A t ht hdim hinj hres g hg n)

include hbase ht hdim hinj hres hsep in
/-- 共通分母と余次元一の有限長な商があれば、通常の Frobenius 商の正規化した長さは
perfection の商の正規化長さへ収束する。
核の長さは零へ収束し、像の長さは商全体の長さへ収束するので、各段の加法性から従う。
文献から別途得る Hilbert–Kunz 極限の値との比較は、極限の一意性に帰着する。 -/
theorem normalized_frobenius_length_tendsto_perfection_quotient [IsNoetherianRing D]
    (H : Ideal D) (hH : IsFiniteLength D (D ⧸ H))
    (g : D) (hg : ∀ c : PerfectClosure D p, PerfectClosure.of D p g * c ∈
      perfectionApproximation D p (Tower A t p) 0)
    {r : ℕ} (hr : r + 1 = h) (z : Fin r → D) (hz : ∀ i, z i ∈ H)
    (hfin : IsFiniteLength D (D ⧸ (Ideal.span {g} ⊔ Ideal.span (Set.range z)))) :
    Filter.Tendsto (fun n : ℕ ↦
      (Module.length D (D ⧸ H.map (iterateFrobenius D p n)) : ℝ≥0∞) /
        (stageRank h p n : ℝ≥0∞)) Filter.atTop
      (nhds (towerLengthFun A t p ((PerfectClosure D p) ⧸ H.map (PerfectClosure.of D p)))) := by
  have hk := towerLengthFun_perfectionApproximation_kernel_tendsto_zero
    A D p t hbase ht hdim hinj hres hsep H hH g hg hr z hz hfin
  have hi := towerLengthFun_perfection_quotientImage_tendsto
    A D p t hbase ht hdim hinj hres hsep H hH
  simp_rw [← towerLengthFun_perfectionApproximation_range_eq_image A D p t] at hi
  have hs := hk.add hi
  simpa only [zero_add, towerLengthFun_perfectionApproximation_kernel_add_range
    A D p t hbase ht hdim hinj hres hsep _ H hH] using hs

end Perfection

end SerrePositivity.Section2

end PerfectApproximationLengthPart

section PerfectQuotientLimitPart

namespace SerrePositivity.Section2

open IsLocalRing
open scoped ENNReal

attribute [local instance] towerPerfectionAlgebra

/-- 準素イデアルの Frobenius 商の正規化した長さは、perfection の商の正規化長さへ収束する。
共通分母と誤差評価用の元の組は、正規性と素イデアル回避によって構成する。 -/
theorem normalized_frobenius_length_tendsto_perfection_quotient_of_primary
    (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing D] [IsDomain D] [IsLocalRing D] [IsNoetherianRing D]
    [Algebra A D] [Module.Finite A D]
    (p : ℕ) [Fact p.Prime] [CharP D p]
    [CharP (ResidueField D) p] [PerfectField (ResidueField D)]
    {h : ℕ} (t : Fin h → A) [Algebra A (PerfectClosure D p)]
    (hbase : ∀ a : A, algebraMap A (PerfectClosure D p) a =
      PerfectClosure.of D p (algebraMap A D a))
    (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hdimA : ringKrullDim A = h) (hdimD : ringKrullDim D = h) (hpos : 0 < h)
    (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable)
    (H : Ideal D) (hH : H.radical = maximalIdeal D) :
    Filter.Tendsto (fun n : ℕ ↦
      (Module.length D (D ⧸ H.map (iterateFrobenius D p n)) : ℝ≥0∞) /
        (stageRank h p n : ℝ≥0∞)) Filter.atTop
      (nhds (towerLengthFun A t p ((PerfectClosure D p) ⧸ H.map (PerfectClosure.of D p)))) := by
  obtain ⟨g, hg, hgc⟩ := exists_tower_perfection_conductor D p A t ht hdimA hinj hres hbase hsep
  have hgD : algebraMap A D g ≠ 0 := fun hz ↦ hg (hinj (hz.trans (map_zero _).symm))
  have hr : h - 1 + 1 = h := Nat.sub_add_cancel hpos
  have hd : ringKrullDim D = (h - 1 : ℕ) + 1 := by
    rw [hdimD]
    exact_mod_cast hr.symm
  obtain ⟨z, hz, hfin⟩ := exists_error_parameters_in_primary
    D H hH (algebraMap A D g) hgD hd
  let : IsArtinianRing (D ⧸ maximalIdeal D) :=
    inferInstanceAs (IsArtinianRing (ResidueField D))
  have hHfin : IsFiniteLength D (D ⧸ H) :=
    isFiniteLength_of_le_radical_annihilator (maximalIdeal D) (D ⧸ H) (by
      rw [Ideal.annihilator_quotient, hH])
  exact normalized_frobenius_length_tendsto_perfection_quotient
    A D p t hbase ht hdimA hinj hres hsep H hHfin (algebraMap A D g) hgc hr z hz hfin

/-- 基底の作用と両立する任意の塔作用で、perfection の商の `λ_D` は同じ Frobenius 極限になる。
完全環への塔の写像の一意性で標準作用へ戻し、定理2.5の `towerLengthOn` の形に接続する。 -/
theorem normalized_frobenius_length_tendsto_towerLengthOn_quotient
    (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing D] [IsDomain D] [IsLocalRing D] [IsNoetherianRing D]
    [Algebra A D] [Module.Finite A D]
    (p : ℕ) [Fact p.Prime] [CharP D p]
    [CharP (ResidueField D) p] [PerfectField (ResidueField D)]
    {h : ℕ} (t : Fin h → A)
    (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hdimA : ringKrullDim A = h) (hdimD : ringKrullDim D = h) (hpos : 0 < h)
    (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable)
    [Algebra A (PerfectClosure D p)] [Algebra D (PerfectClosure D p)]
    [instTower : Algebra (Tower A t p) (PerfectClosure D p)]
    [IsScalarTower A D (PerfectClosure D p)]
    [IsScalarTower A (Tower A t p) (PerfectClosure D p)]
    (hcanonical : algebraMap D (PerfectClosure D p) = PerfectClosure.of D p)
    (H : Ideal D) (hH : H.radical = maximalIdeal D) :
    Filter.Tendsto (fun n : ℕ ↦
      (Module.length D (D ⧸ H.map (iterateFrobenius D p n)) : ℝ≥0∞) /
        (stageRank h p n : ℝ≥0∞)) Filter.atTop
      (nhds ((towerLengthOn A D hinj t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) (PerfectClosure D p)).len
        ((PerfectClosure D p) ⧸ H.map (algebraMap D (PerfectClosure D p))))) := by
  have heq : instTower = towerPerfectionAlgebra A D p t := by
    apply Algebra.algebra_ext
    intro x
    exact AlgHom.congr_fun (towerToPerfect_unique A (PerfectClosure D p) t p
      (IsScalarTower.toAlgHom A (Tower A t p) (PerfectClosure D p))) x
  subst instTower
  have hbase : ∀ a : A, algebraMap A (PerfectClosure D p) a =
      PerfectClosure.of D p (algebraMap A D a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply A D (PerfectClosure D p), hcanonical]
  have hI : H.map (algebraMap D (PerfectClosure D p)) = H.map (PerfectClosure.of D p) := by
    rw [hcanonical]
  rw [hI]
  exact normalized_frobenius_length_tendsto_perfection_quotient_of_primary
    A D p t hbase ht hdimA hdimD hpos hinj hres hsep H hH

set_option backward.isDefEq.respectTransparency false in
/-- 高次 Frobenius Koszul ホモロジーの正規化長さの零への収束から、
perfection のパラメータ商の正規化長さを Hilbert–Samuel 重複度と同定する。
共通分母・有限段の誤差評価・Euler 公式・極限の一意性を組み合わせる。
高次ホモロジーの消滅極限そのものは、この定理の前提として明示する。 -/
theorem towerLengthOn_perfection_parameter_quotient_eq_multiplicity_of_higher_tendsto
    (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing D] [IsDomain D] [IsLocalRing D] [IsNoetherianRing D]
    [Algebra A D] [Module.Finite A D]
    (p : ℕ) [Fact p.Prime] [CharP D p]
    [CharP (ResidueField D) p] [PerfectField (ResidueField D)]
    {h : ℕ} (t : Fin h → A)
    (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hdimA : ringKrullDim A = h) (hdimD : ringKrullDim D = h) (hpos : 0 < h)
    (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable)
    [Algebra A (PerfectClosure D p)] [Algebra D (PerfectClosure D p)]
    [Algebra (Tower A t p) (PerfectClosure D p)]
    [IsScalarTower A D (PerfectClosure D p)]
    [IsScalarTower A (Tower A t p) (PerfectClosure D p)]
    (hcanonical : algebraMap D (PerfectClosure D p) = PerfectClosure.of D p)
    (z : Fin h → D) (hz : IsSystemOfParameters D z)
    (hlim : ∀ i : ℤ, i < 0 → Filter.Tendsto (fun n : ℕ ↦
      (Module.length D ((koszulComplex (fun j ↦ z j ^ (p ^ n))).homology i) : ℝ≥0∞) /
        (stageRank h p n : ℝ≥0∞)) Filter.atTop (nhds 0)) :
    (towerLengthOn A D hinj t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) (PerfectClosure D p)).len
      ((PerfectClosure D p) ⧸
        Ideal.span (Set.range fun j ↦ algebraMap D (PerfectClosure D p) (z j))) =
      ENNReal.ofReal (HilbertSamuel.multiplicity D (Ideal.span (Set.range z)) D : ℝ) := by
  have hlength := normalized_frobenius_length_tendsto_towerLengthOn_quotient
    A D p t ht hdimA hdimD hpos hinj hres hsep hcanonical (Ideal.span (Set.range z)) hz.2
  have he := HilbertSamuel.normalized_parameter_quotient_tendsto_ennreal_of_higher_koszul
    D z hz (fun n ↦ p ^ n) (fun n ↦ pow_pos (Fact.out : p.Prime).pos n)
    (fun i hi ↦ by
      simpa only [stageRank, pow_mul, Nat.cast_pow] using hlim i hi)
  have hstage (n : ℕ) :
      Module.length D (D ⧸ (Ideal.span (Set.range z)).map (iterateFrobenius D p n)) =
        Module.length D (D ⧸ Ideal.span (Set.range fun j ↦ z j ^ (p ^ n))) := by
    apply congrArg (fun I : Ideal D ↦ Module.length D (D ⧸ I))
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have htarget :
      (towerLengthOn A D hinj t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) (PerfectClosure D p)).len
        ((PerfectClosure D p) ⧸
          (Ideal.span (Set.range z)).map (algebraMap D (PerfectClosure D p))) =
      (towerLengthOn A D hinj t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) (PerfectClosure D p)).len
        ((PerfectClosure D p) ⧸
          Ideal.span (Set.range fun j ↦ algebraMap D (PerfectClosure D p) (z j))) := by
    apply congrArg (fun I : Ideal (PerfectClosure D p) ↦
      (towerLengthOn A D hinj t p
        (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) (PerfectClosure D p)).len
          ((PerfectClosure D p) ⧸ I))
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have hlength' : Filter.Tendsto (fun n : ℕ ↦
      (Module.length D (D ⧸ Ideal.span (Set.range fun j ↦ z j ^ (p ^ n))) : ℝ≥0∞) /
        ((p ^ n : ℕ) : ℝ≥0∞) ^ h) Filter.atTop
      (nhds ((towerLengthOn A D hinj t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) (PerfectClosure D p)).len
        ((PerfectClosure D p) ⧸
          Ideal.span (Set.range fun j ↦ algebraMap D (PerfectClosure D p) (z j))))) := by
    simpa only [hstage, htarget, stageRank, pow_mul, Nat.cast_pow] using hlength
  exact tendsto_nhds_unique hlength' he

end SerrePositivity.Section2

end PerfectQuotientLimitPart

section PerfectKoszulLengthPart

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

end PerfectKoszulLengthPart

section PerfectKoszulLimitPart

namespace SerrePositivity.Section2

open IsLocalRing CategoryTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

attribute [local instance] rootStageAlgebra towerPerfectionAlgebra stagePerfectionAlgebra
  stageTowerPerfection

variable (A D : Type u) [CommRing A] [CommRing D] [IsDomain D]
    (p : ℕ) [Fact p.Prime] [CharP D p] [Algebra A (PerfectClosure D p)]
    {h : ℕ} (t : Fin h → A)

/-- 初段から各近似段へ送った元は、元の環からその段への標準写像と一致する。 -/
theorem perfectionApproximation_stageBaseMap (n : ℕ) (d : D) :
    subalgebraStageBaseMap (Tower A t p) (PerfectClosure D p)
      (perfectionApproximation D p (Tower A t p))
      (perfectionApproximation_monotone D p (Tower A t p)) n
      (perfectionApproximationBaseMap A D p t 0 d) =
        perfectionApproximationBaseMap A D p t n d := by
  apply Subtype.ext
  rw [subalgebraStageBaseMap_coe, perfectionApproximationBaseMap_coe,
    perfectionApproximationBaseMap_coe]

/-- Perfection の近似環の Koszul 図式。全段を塔上の複体として扱う。 -/
noncomputable abbrev perfectionKoszulDiagram {r : ℕ} (z : Fin r → D) :=
  subalgebraKoszulDiagram (Tower A t p) (PerfectClosure D p)
    (perfectionApproximation D p (Tower A t p))
    (perfectionApproximation_monotone D p (Tower A t p))
    (perfectionApproximationBaseMap A D p t 0 ∘ z)

/-- 近似環の Koszul ホモロジーの有向極限は、perfection のホモロジーに塔上で同型。 -/
noncomputable def perfectionKoszulHomologyDirectLimitEquiv {r : ℕ}
    (z : Fin r → D) (i : ℤ) :
    Module.DirectLimit (fun n ↦ ((perfectionKoszulDiagram A D p t z).obj n).homology i)
      (homologyStageMap (perfectionKoszulDiagram A D p t z) i) ≃ₗ[Tower A t p]
      (ModuleCat.restrictScalars (algebraMap (Tower A t p) (PerfectClosure D p))).obj
        ((koszulComplex (PerfectClosure.of D p ∘ z)).homology i) := by
  have e := subalgebraKoszulHomologyDirectLimitEquiv (Tower A t p) (PerfectClosure D p)
    (perfectionApproximation D p (Tower A t p))
    (perfectionApproximation_monotone D p (Tower A t p))
    (perfectionApproximationBaseMap A D p t 0 ∘ z)
    (exists_mem_perfectionApproximation D p (Tower A t p)) i
  have he : (perfectionApproximation D p (Tower A t p) 0).val ∘
      (perfectionApproximationBaseMap A D p t 0 ∘ z) = PerfectClosure.of D p ∘ z := by
    funext j
    exact perfectionApproximationBaseMap_coe A D p t 0 (z j)
  rw [he] at e
  exact e

variable [IsRegularLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    [IsLocalRing D] [IsNoetherianRing D] [Algebra A D] [Module.Finite A D]
    [CharP (ResidueField D) p] [PerfectField (ResidueField D)]

/-- 高次 Frobenius Koszul ホモロジーの通常長さの消滅極限を、perfection 上の消滅へ移す。
近似段の有限長性・平坦性・共通の消去冪・有向被覆は元の仮定から供給する。 -/
theorem towerLengthFun_perfection_koszulHomology_eq_zero_of_tendsto
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (hdim : ringKrullDim A = h)
    (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    (hbase : ∀ a : A, algebraMap A (PerfectClosure D p) a =
      PerfectClosure.of D p (algebraMap A D a))
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable)
    (z : Fin h → D) (hz : IsSystemOfParameters D z) (i : ℤ)
    (hlim : Filter.Tendsto (fun n : ℕ ↦
      (Module.length D ((koszulComplex (fun j ↦ z j ^ (p ^ n))).homology i) : ℝ≥0∞) /
        (stageRank h p n : ℝ≥0∞)) Filter.atTop (nhds 0)) :
    letI := Module.compHom ((koszulComplex (PerfectClosure.of D p ∘ z)).homology i)
      (algebraMap (Tower A t p) (PerfectClosure D p))
    towerLengthFun A t p ((koszulComplex (PerfectClosure.of D p ∘ z)).homology i) = 0 := by
  have htm : ∀ j, t j ∈ maximalIdeal A :=
    fun j ↦ ht ▸ Ideal.subset_span (Set.mem_range_self j)
  let R := Tower A t p
  let C := PerfectClosure D p
  let B := perfectionApproximation D p R
  let hB := perfectionApproximation_monotone D p R
  let z₀ := perfectionApproximationBaseMap A D p t 0 ∘ z
  have he (n : ℕ) : subalgebraStageBaseMap R C B hB n ∘ z₀ =
      perfectionApproximationBaseMap A D p t n ∘ z := by
    funext j
    exact perfectionApproximation_stageBaseMap A D p t n (z j)
  obtain ⟨N, hN⟩ := exists_uniform_pow_torsion_perfectionApproximation_koszul
    A D p t hinj hbase z hz
  have hstage (n : ℕ) : (towerLength A t p htm).len
      ((ModuleCat.restrictScalars (algebraMap R (B n))).obj
        ((koszulComplex (subalgebraStageBaseMap R C B hB n ∘ z₀)).homology i)) =
      (Module.length D ((koszulComplex (fun j ↦ z j ^ (p ^ n))).homology i) : ℝ≥0∞) /
        (stageRank h p n : ℝ≥0∞) := by
    rw [he]
    exact (perfectionApproximation_koszulHomology_length
      A D p t ht hdim hinj hres hbase hsep n z hz i).1
  have hzlim := subalgebraKoszulHomology_len_eq_zero R C B hB z₀
    (exists_mem_perfectionApproximation D p R) (towerLength A t p htm)
    (towerLength_hasSup A t p htm) i N (fun n ↦ by
      rw [he]
      exact hN n i) (by
        have heq : (fun n ↦ (towerLength A t p htm).len
            ((ModuleCat.restrictScalars (algebraMap R (B n))).obj
              ((koszulComplex (subalgebraStageBaseMap R C B hB n ∘ z₀)).homology i))) =
            (fun n ↦ (Module.length D
              ((koszulComplex (fun j ↦ z j ^ (p ^ n))).homology i) : ℝ≥0∞) /
                (stageRank h p n : ℝ≥0∞)) := funext hstage
        rw [heq]
        exact hlim)
  have he₀ : (B 0).val ∘ z₀ = PerfectClosure.of D p ∘ z := by
    funext j
    exact perfectionApproximationBaseMap_coe A D p t 0 (z j)
  rw [he₀] at hzlim
  exact hzlim

/-- 任意の両立する塔作用について、同じ消滅を定理2.5の `λ_D` と homological 添字で述べる。 -/
theorem towerLengthOn_perfection_koszulHomology_eq_zero_of_tendsto
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (hdim : ringKrullDim A = h)
    (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable)
    [Algebra D (PerfectClosure D p)]
    [instTower : Algebra (Tower A t p) (PerfectClosure D p)]
    [IsScalarTower A D (PerfectClosure D p)]
    [IsScalarTower A (Tower A t p) (PerfectClosure D p)]
    (hcanonical : algebraMap D (PerfectClosure D p) = PerfectClosure.of D p)
    (z : Fin h → D) (hz : IsSystemOfParameters D z) (i : ℕ)
    (hlim : Filter.Tendsto (fun n : ℕ ↦
      (Module.length D (koszulHomologySelf (fun j ↦ z j ^ (p ^ n)) i) : ℝ≥0∞) /
        (stageRank h p n : ℝ≥0∞)) Filter.atTop (nhds 0)) :
    (towerLengthOn A D hinj t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) (PerfectClosure D p)).len
      (koszulHomologySelf (algebraMap D (PerfectClosure D p) ∘ z) i) = 0 := by
  have heq : instTower = towerPerfectionAlgebra A D p t := by
    apply Algebra.algebra_ext
    intro x
    exact AlgHom.congr_fun (towerToPerfect_unique A (PerfectClosure D p) t p
      (IsScalarTower.toAlgHom A (Tower A t p) (PerfectClosure D p))) x
  subst instTower
  have hbase : ∀ a : A, algebraMap A (PerfectClosure D p) a =
      PerfectClosure.of D p (algebraMap A D a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply A D (PerfectClosure D p), hcanonical]
  have he : algebraMap D (PerfectClosure D p) ∘ z = PerfectClosure.of D p ∘ z := by
    rw [hcanonical]
  rw [he]
  exact towerLengthFun_perfection_koszulHomology_eq_zero_of_tendsto
    A D p t ht hdim hinj hres hbase hsep z hz (-(i : ℤ)) hlim

end SerrePositivity.Section2

end PerfectKoszulLimitPart
