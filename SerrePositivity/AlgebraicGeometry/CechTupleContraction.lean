module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Tactic.Abel

/-!
概要：全タプルの増大整数鎖の、頂点を先頭に付ける縮約。
方針：境界のうち先頭を削除する項を分離し、残る項の符号を反転する。
規約：鎖の添字はタプルの長さであり、長さ零が増大項に対応する。
使われ方：標準開の Čech 比較で、各タプルの頂点集合内にホモトピーを作る。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped BigOperators

variable {ι : Type*}

/-- 長さ `k` のタプルを生成元とする自由整数加群。 -/
abbrev CechTupleChains (ι : Type*) (k : ℕ) := (Fin k → ι) →₀ ℤ

/-- 各頂点の削除の交代和で定める境界。 -/
def cechTupleBoundary (k : ℕ) : CechTupleChains ι (k + 1) →ₗ[ℤ] CechTupleChains ι k :=
  Finsupp.linearCombination ℤ fun t ↦
    ∑ i : Fin (k + 1), (-1 : ℤ) ^ i.val • Finsupp.single (t ∘ i.succAbove) 1

private theorem cechTupleBoundary_single (k : ℕ) (t : Fin (k + 1) → ι) :
    cechTupleBoundary k (Finsupp.single t 1) =
      ∑ i : Fin (k + 1), (-1 : ℤ) ^ i.val • Finsupp.single (t ∘ i.succAbove) 1 := by
  simp only [cechTupleBoundary, Finsupp.linearCombination_single, one_smul]

open CategoryTheory

universe u

private def cechTupleSimplicialModule (ι : Type u) : SimplicialObject (ModuleCat.{u} ℤ) where
  obj n := ModuleCat.of ℤ (CechTupleChains ι (n.unop.len + 1))
  map f := ModuleCat.ofHom (Finsupp.lmapDomain ℤ ℤ (fun t ↦ t ∘ f.unop.toOrderHom))
  map_id _ := by
    apply ModuleCat.hom_ext
    exact Finsupp.lmapDomain_id _ _
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact Finsupp.lmapDomain_comp _ _ (fun t ↦ t ∘ f.unop.toOrderHom)
      (fun t ↦ t ∘ g.unop.toOrderHom)

private theorem cechTupleSimplicialModule_objD (k : ℕ) :
    (AlgebraicTopology.AlternatingFaceMapComplex.objD (cechTupleSimplicialModule ι) k).hom =
      cechTupleBoundary (k + 1) := by
  apply Finsupp.lhom_ext
  intro t c
  have hd (i : Fin (k + 2)) : ((cechTupleSimplicialModule ι).δ i).hom =
      Finsupp.lmapDomain ℤ ℤ (fun a : Fin (k + 2) → ι ↦ a ∘ i.succAbove) := rfl
  simp only [AlgebraicTopology.AlternatingFaceMapComplex.objD, ModuleCat.hom_sum,
    ModuleCat.hom_zsmul, hd]
  change (Fin (k + 2) → ι) at t
  let d : CechTupleChains ι (k + 2) →ₗ[ℤ] CechTupleChains ι (k + 1) :=
    ∑ i : Fin (k + 2), (-1 : ℤ) ^ i.val •
      Finsupp.lmapDomain ℤ ℤ (fun a : Fin (k + 2) → ι ↦ a ∘ i.succAbove)
  change d (Finsupp.single t c) = cechTupleBoundary (k + 1) (Finsupp.single t c)
  have e : d (Finsupp.single t 1) = cechTupleBoundary (k + 1) (Finsupp.single t 1) := by
    dsimp only [d]
    rw [LinearMap.sum_apply, cechTupleBoundary_single]
    simp only [LinearMap.smul_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rw [← Finsupp.smul_single_one t c]
  exact (map_zsmul d c _).trans ((congrArg (c • ·) e).trans
    (map_zsmul (cechTupleBoundary (ι := ι) (k + 1)) c _).symm)

/--
概要：全タプルの増大鎖の境界を二回適用すると零になる。
方針：正次数は自由単体加群の交代境界を使い、増大項は二つの面を直接比較する。
規約：長さ零は空タプルの自由加群とする。
使われ方：Čech 比較ホモトピーで補正項がサイクルになることを示す。
-/
theorem cechTupleBoundary_squared (k : ℕ) (x : CechTupleChains ι (k + 2)) :
    cechTupleBoundary k (cechTupleBoundary (k + 1) x) = 0 := by
  cases k with
  | zero =>
    have hε (t : Fin 1 → ι) :
        cechTupleBoundary 0 (Finsupp.single t 1) = Finsupp.single Fin.elim0 1 := by
      rw [cechTupleBoundary_single, Fin.sum_univ_succ]
      simp
    have h : (cechTupleBoundary (ι := ι) 0).comp (cechTupleBoundary 1) = 0 := by
      apply Finsupp.lhom_ext
      intro t c
      rw [← Finsupp.smul_single_one t c, map_smul, LinearMap.zero_apply]
      suffices h : cechTupleBoundary 0 (cechTupleBoundary 1 (Finsupp.single t 1)) = 0 by
        simp [LinearMap.comp_apply, h]
      simp [cechTupleBoundary_single 1, Fin.sum_univ_two, map_add, map_neg, hε]
    exact LinearMap.congr_fun h x
  | succ k =>
    have h := congrArg ModuleCat.Hom.hom
      (AlgebraicTopology.AlternatingFaceMapComplex.d_squared (cechTupleSimplicialModule ι) k)
    rw [ModuleCat.hom_comp, ModuleCat.hom_zero, cechTupleSimplicialModule_objD,
      cechTupleSimplicialModule_objD] at h
    exact LinearMap.congr_fun h x

/-- 固定頂点を各タプルの先頭に付ける。 -/
def cechTuplePrepend (v : ι) (k : ℕ) :
    CechTupleChains ι k →ₗ[ℤ] CechTupleChains ι (k + 1) :=
  Finsupp.lmapDomain ℤ ℤ (fun t : Fin k → ι ↦ Fin.cons v t)

private theorem cechTuplePrepend_single (v : ι) (k : ℕ) (t : Fin k → ι) :
    cechTuplePrepend v k (Finsupp.single t 1) = Finsupp.single (Fin.cons v t) 1 := by
  simp only [cechTuplePrepend, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/--
概要：正の長さのタプルで境界と先頭追加の反交換式を与える。
方針：先頭を削除した項が恒等で、他の削除が先頭追加と反対の符号で対応する。
規約：長さ一の式には、長さ零への増大写像が入る。
使われ方：各タプルの頂点集合内でサイクルの境界前像を作る。
-/
theorem cechTupleBoundary_prepend (v : ι) (k : ℕ) :
    (cechTupleBoundary (k + 1)).comp (cechTuplePrepend v (k + 1)) +
      (cechTuplePrepend v k).comp (cechTupleBoundary k) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro t c
  rw [← Finsupp.smul_single_one t c, map_smul, map_smul]
  congr 1
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    cechTuplePrepend_single, cechTupleBoundary_single, map_sum, map_smul]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero, Fin.cons_comp_succ,
    Fin.val_succ, pow_succ, mul_neg_one, neg_smul, Fin.cons_comp_succ_succAbove,
    Finset.sum_neg_distrib, add_assoc]
  have hface (i : Fin (k + 1)) : i.removeNth t = t ∘ i.succAbove := rfl
  simp only [hface, neg_add_cancel, add_zero]

/--
概要：全タプルの恒等鎖写像と、増加タプルを経由する鎖写像 P の間のホモトピー候補。
方針：生成元ごとに、前の次数で残った差へ先頭追加の縮約を適用する。
規約：長さ零の成分は零。各正長タプルではその先頭を縮約の頂点とする。
使われ方：P が境界と可換で添字集合を増やさない場合に、係数付き Čech 比較へ移す。
-/
def cechTupleComparisonHomotopy
    (P : ∀ k, CechTupleChains ι k →ₗ[ℤ] CechTupleChains ι k) :
    (k : ℕ) → CechTupleChains ι k →ₗ[ℤ] CechTupleChains ι (k + 1)
  | 0 => 0
  | k + 1 => Finsupp.linearCombination ℤ fun t ↦
      cechTuplePrepend (t 0) (k + 1)
        (Finsupp.single t 1 - P (k + 1) (Finsupp.single t 1) -
          cechTupleComparisonHomotopy P k (cechTupleBoundary k (Finsupp.single t 1)))

theorem cechTupleComparisonHomotopy_succ_single
    (P : ∀ k, CechTupleChains ι k →ₗ[ℤ] CechTupleChains ι k)
    (k : ℕ) (t : Fin (k + 1) → ι) :
    cechTupleComparisonHomotopy P (k + 1) (Finsupp.single t 1) =
      cechTuplePrepend (t 0) (k + 1)
        (Finsupp.single t 1 - P (k + 1) (Finsupp.single t 1) -
          cechTupleComparisonHomotopy P k (cechTupleBoundary k (Finsupp.single t 1))) := by
  simp only [cechTupleComparisonHomotopy, Finsupp.linearCombination_single, one_smul]

/-- すべての頂点が T に入るタプルで生成される部分鎖加群。 -/
def cechTupleChainsOn (T : Set ι) (k : ℕ) : Submodule ℤ (CechTupleChains ι k) :=
  Finsupp.supported ℤ ℤ {t | ∀ i, t i ∈ T}

private theorem cechTupleChainsOn_single {T : Set ι} {k : ℕ} {t : Fin k → ι}
    (ht : ∀ i, t i ∈ T) : Finsupp.single t (1 : ℤ) ∈ cechTupleChainsOn T k :=
  Finsupp.single_mem_supported ℤ 1 ht

private theorem cechTupleChainsOn_le_comap {T : Set ι} {k l : ℕ}
    (f : CechTupleChains ι k →ₗ[ℤ] CechTupleChains ι l)
    (h : ∀ (t : Fin k → ι), (∀ i, t i ∈ T) →
      f (Finsupp.single t 1) ∈ cechTupleChainsOn T l) :
    cechTupleChainsOn T k ≤ (cechTupleChainsOn T l).comap f := by
  change Finsupp.supported ℤ ℤ {t : Fin k → ι | ∀ i, t i ∈ T} ≤ _
  rw [Finsupp.supported_eq_span_single, Submodule.span_le]
  rintro _ ⟨t, ht, rfl⟩
  exact h t ht

private theorem cechTupleBoundary_mem_chainsOn {T : Set ι} {k : ℕ}
    {x : CechTupleChains ι (k + 1)} (hx : x ∈ cechTupleChainsOn T (k + 1)) :
    cechTupleBoundary k x ∈ cechTupleChainsOn T k := by
  apply cechTupleChainsOn_le_comap (cechTupleBoundary k) _ hx
  intro t ht
  rw [cechTupleBoundary_single]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _
    (cechTupleChainsOn_single fun j ↦ ht (i.succAbove j))

private theorem cechTuplePrepend_mem_chainsOn {T : Set ι} {v : ι} (hv : v ∈ T) {k : ℕ}
    {x : CechTupleChains ι k} (hx : x ∈ cechTupleChainsOn T k) :
    cechTuplePrepend v k x ∈ cechTupleChainsOn T (k + 1) := by
  apply cechTupleChainsOn_le_comap (cechTuplePrepend v k) _ hx
  intro t ht
  rw [cechTuplePrepend_single]
  exact cechTupleChainsOn_single (Fin.cases (by simpa using hv) (fun i ↦ by simpa using ht i))

/--
概要：ホモトピーの各項の頂点は、入力タプルの頂点集合に収まる。
方針：境界と先頭追加が頂点集合を保つことを使い、長さで帰納する。
規約：P が任意の頂点部分集合に対応する鎖加群を保つとする。
使われ方：鎖ホモトピーを制限写像付きの Čech コチェインに移す。
-/
theorem cechTupleComparisonHomotopy_mem_chainsOn
    (P : ∀ k, CechTupleChains ι k →ₗ[ℤ] CechTupleChains ι k)
    (hP : ∀ T k (x : CechTupleChains ι k),
      x ∈ cechTupleChainsOn T k → P k x ∈ cechTupleChainsOn T k)
    (T : Set ι) (k : ℕ) (x : CechTupleChains ι k) (hx : x ∈ cechTupleChainsOn T k) :
    cechTupleComparisonHomotopy P k x ∈ cechTupleChainsOn T (k + 1) := by
  induction k with
  | zero => exact (cechTupleChainsOn T 1).zero_mem
  | succ k ih =>
    apply cechTupleChainsOn_le_comap (cechTupleComparisonHomotopy P (k + 1)) _ hx
    intro t ht
    rw [cechTupleComparisonHomotopy_succ_single]
    have hs := cechTupleChainsOn_single ht
    exact cechTuplePrepend_mem_chainsOn (ht 0) <|
      (cechTupleChainsOn T (k + 1)).sub_mem
        ((cechTupleChainsOn T (k + 1)).sub_mem hs (hP T _ _ hs))
        (ih _ (cechTupleBoundary_mem_chainsOn hs))

private theorem cechTupleComparisonHomotopy_zero
    (P : ∀ k, CechTupleChains ι k →ₗ[ℤ] CechTupleChains ι k) :
    cechTupleComparisonHomotopy P 0 = 0 := rfl

private theorem cechTupleBoundary_prepend_of_cycle (v : ι) (k : ℕ)
    (z : CechTupleChains ι (k + 1)) (hz : cechTupleBoundary k z = 0) :
    cechTupleBoundary (k + 1) (cechTuplePrepend v (k + 1) z) = z := by
  simpa [LinearMap.comp_apply, hz] using
    LinearMap.congr_fun (cechTupleBoundary_prepend v k) z

set_option maxHeartbeats 1000000 in
-- 帰納段で生成元上の等式を線形写像の等式に戻す際、局所的に上限を上げる。
/--
概要：増大項で恒等な鎖写像 P に対し、帰納定義したホモトピーの方程式を示す。
方針：境界と P の可換性および一つ下の次数の式から、各生成元の補正項がサイクルになる。
規約：長さ零で P は恒等とする。
使われ方：狭義増加タプルを経由する鎖写像の合成を恒等と比較する。
-/
theorem cechTupleComparisonHomotopy_identity
    (P : ∀ k, CechTupleChains ι k →ₗ[ℤ] CechTupleChains ι k)
    (hP0 : P 0 = LinearMap.id)
    (hP : ∀ k (x : CechTupleChains ι (k + 1)),
      cechTupleBoundary k (P (k + 1) x) = P k (cechTupleBoundary k x))
    (k : ℕ) :
    (cechTupleBoundary (k + 1)).comp (cechTupleComparisonHomotopy P (k + 1)) +
      (cechTupleComparisonHomotopy P k).comp (cechTupleBoundary k) = LinearMap.id - P (k + 1) := by
  induction k with
  | zero =>
    apply Finsupp.lhom_ext
    intro t c
    rw [← Finsupp.smul_single_one t c, map_smul, map_smul]
    congr 1
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      cechTupleComparisonHomotopy_succ_single, cechTupleComparisonHomotopy_zero,
      LinearMap.zero_apply, sub_zero, add_zero]
    apply cechTupleBoundary_prepend_of_cycle
    rw [map_sub, hP, hP0, LinearMap.id_apply, sub_self]
  | succ k ih =>
    apply Finsupp.lhom_ext
    intro t c
    rw [← Finsupp.smul_single_one t c, map_smul, map_smul]
    congr 1
    let x : CechTupleChains ι (k + 2) := Finsupp.single t 1
    have hprev : cechTupleBoundary (k + 1)
        (cechTupleComparisonHomotopy P (k + 1) (cechTupleBoundary (k + 1) x)) =
        cechTupleBoundary (k + 1) x - P (k + 1) (cechTupleBoundary (k + 1) x) := by
      simpa [LinearMap.comp_apply, cechTupleBoundary_squared] using
        LinearMap.congr_fun ih (cechTupleBoundary (k + 1) x)
    have hz : cechTupleBoundary (k + 1)
        (x - P (k + 2) x -
          cechTupleComparisonHomotopy P (k + 1) (cechTupleBoundary (k + 1) x)) = 0 := by
      rw [map_sub, map_sub, hP, hprev, sub_self]
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      cechTupleComparisonHomotopy_succ_single]
    change cechTupleBoundary (k + 2)
        (cechTuplePrepend (t 0) (k + 2)
          (x - P (k + 2) x -
            cechTupleComparisonHomotopy P (k + 1) (cechTupleBoundary (k + 1) x))) +
        cechTupleComparisonHomotopy P (k + 1) (cechTupleBoundary (k + 1) x) = x - P (k + 2) x
    rw [cechTupleBoundary_prepend_of_cycle _ _ _ hz]
    abel

end SerrePositivity.AlgebraicGeometry
