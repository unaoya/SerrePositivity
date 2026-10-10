module

public import SerrePositivity.Paper.Section2.PerfectConductor
public import SerrePositivity.Paper.Section2.TowerDescent
public import SerrePositivity.CommutativeAlgebra.QuotientPowerLength
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# 近似環の商の正規化長さ

有限段からの係数拡大と商を交換し、近似環の商を有限段の商加群から得る。
正規化長さは、その段の通常の長さを `p^(nh)` で割った値になる。
有限長性から冪ねじれ条件を導くので、利用側には有限長性だけを要求する。
Frobenius 同型と剰余体の一致を用いて、有限段上の長さを元の環 `D` 上の長さに戻す。
特に論文の `B_q/(HB_q + g^(1/q)B_q)` の公式を得る。
`g` と合わせて有限長の商を作る `h-1` 個の元が `H` 内にあれば、
生成元の冪による長さ評価から、この正規化長さが零へ収束することも示す。
初段の共通分母があれば、商写像の核も同じ評価で零へ収束する。
各段で核と像の長さの和を通常の Frobenius 商の長さで表す等式も得る。
固定した商の中の像は増大して全体を覆うので、その長さは商全体の長さに収束する。
したがって共通分母と上記の元の組を与えれば、通常の Frobenius 商の正規化した長さは
perfection の商の正規化長さへ収束する。
長さの公式は既存の Lemma 2.3 (b) の引用入力 (C1) に依存する。
具体的な近似環との接続では、正則パラメータの未証明入力も用いる。
-/

public section
universe u
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

variable (A D : Type u) [CommRing A] [IsLocalRing A] [CommRing D]
    (p : ℕ) [Fact p.Prime] [CharP D p] {h : ℕ} (t : Fin h → A)
    [Algebra A (PerfectClosure D p)]

/-- 冪ねじれな perfection の商の長さは、近似部分代数から来る像の長さの上限。
像の増大・被覆と、既存の正規化長さの上限性を組み合わせる。 -/
theorem towerLengthFun_quotient_eq_iSup_image (J : Ideal (PerfectClosure D p))
    (hJ : IsPowTorsion (towerMaxIdeal A t p) ((PerfectClosure D p) ⧸ J)) :
    towerLengthFun A t p ((PerfectClosure D p) ⧸ J) =
      ⨆ n, towerLengthFun A t p (perfectionQuotientImage D p (Tower A t p) J n) := by
  have he := NormalizedLength.len_iSup_of_directed (towerLength_hasSup A t p) hJ
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
  rw [towerLengthFun_quotient_eq_iSup_image A D p t J hJ]
  apply tendsto_atTop_iSup
  intro n m hnm
  exact (towerLength A t p).len_le_of_injective
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
  have hb := perfectionApproximation_kernel_bound D p (Tower A t p) (towerLength A t p)
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
  towerLengthFun_quotientImage_tendsto A D p t _
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
  have hs := (towerLength A t p).len_eq_add_ker_range f
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
