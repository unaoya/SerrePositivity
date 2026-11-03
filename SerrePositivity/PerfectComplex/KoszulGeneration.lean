module

public import SerrePositivity.CommutativeAlgebra.Length.Euler
public import SerrePositivity.PerfectComplex.Truncate
public import SerrePositivity.PerfectComplex.Free.K0
public import SerrePositivity.CommutativeAlgebra.Length.Basic
public import SerrePositivity.CommutativeAlgebra.Koszul.Resolution
public import SerrePositivity.PerfectComplex.Free.Euler

/-!
# `K₀^{m}(A)` は Koszul 複体で生成される

## 概要

`A` を Noether 局所環、`z` を極大イデアル `m_A` を生成する列で、Koszul 複体 `K(z)` が `A/(z) = k` の
分解（`IsKoszulResolution z`）になるものとする。このとき、`z` に台をもつ完全 `A` 複体 `Q` の類は
`[K(z)]` の整数倍である：`[Q] = m · [K(z)]`（`K0.exists_eq_zsmul_koszul`）。したがって `K₀^{m}(A)`
からの準同型は `[K(z)]` での値で決まる（`K0.hom_ext_koszul`）。

これは論文 Lemma 3.5b の証明の核心「`K_0^{m}(A)` は `[K(z)]` で生成される」で、通常の長さ版と
正規化長さ版（どちらも `Paper/Section3/NormComparison.lean`）の共通の入力に
なる。正則局所環の正則パラメータ系なら `IsKoszulResolution z` は `CommutativeAlgebra/RegularLocalRing.lean` の
A1（正則列）から出る（`CommutativeAlgebra/Koszul/Resolution.lean`）。正則性はこの仮定を通してだけ使う。

## 証明（デヴィサージュ）

ホモロジーの長さの総和 `homologyLengthSum Q`（`CommutativeAlgebra/HomologyLength.lean`）についての
強い帰納法。台つき完全複体のホモロジーは有限長（`OrdinaryEuler.lean`）なので総和は意味をもつ。
シフトで最上段を `0` 次にそろえ（`[Q⟦n⟧] = ±[Q]`）、

- `H^0(Q) ≠ 0` なら、全射 `H^0(Q) → k`（`FiniteLength.lean` の `exists_surjective_quotient_span`）から
  射 `Q → k[0]` を作り、擬同型 `K(z) → k[0]`（`koszulAugmentation`）に沿って `f : Q → K(z)` に持ち上げる
  （`Q` は項が射影的な有界複体なので K 射影的、`HomologicalAlgebra/KProjectiveLift.lean`）。`f` は
  `H^0` で全射なので `Cone f` は長さの総和が 1 小さく（`homologyLengthSum_mappingCone`）、錐の関係式
  から `[Q] = [K(z)] - [Cone f]`。
- `H^0(Q) = 0` なら最上段を切り詰めて（`CommutativeAlgebra/Truncate.lean`）、幅が一つ小さい
  ホモトピー同値な複体に移る。幅についての帰納法で、幅 `0` なら零複体で `[Q] = 0`。

## 内容

- `chiOrd_koszulComplex`：`χ_A(K(z)) = ℓ_A(A/(z)) = 1`。準同型の `[K(z)]` での値の計算に使う。
- `length_homology_ne_top`、`exists_mappingCone_step`：帰納法の一歩。
- `K0.exists_eq_zsmul_koszul`、`K0.hom_ext_koszul`。
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace SerrePositivity

variable {A : Type u} [CommRing A] [IsLocalRing A] {e : ℕ} {z : Fin e → A}

/-! ## Koszul 複体の Euler 評価 -/

section koszul

variable (hK : IsKoszulResolution z)

include hK in
/-- `z` が `m_A` を生成し `K(z)` が `A/(z)` の分解なら、`χ_A(K(z)) = ℓ_A(A/(z)) = ℓ_A(k) = 1`。
ホモロジーは `0` 次の `A/(z) = A/m_A` に集中し、剰余体は長さ `1` だから。Lemma 3.5b で通常の
長さ側の準同型の `[K(z)]` での値になる。 -/
theorem chiOrd_koszulComplex (hz : Ideal.span (Set.range z) = maximalIdeal A) :
    chiOrd (koszulComplex z) = 1 := by
  unfold chiOrd
  rw [finsum_eq_single _ (0 : ℤ)]
  · rw [Int.negOnePow_zero, Units.val_one, Int.cast_one, one_mul,
      (koszulH0Iso hK).toLinearEquiv.length_eq]
    have := isSimpleModule_quotient_span_of_eq hz
    rw [Module.length_eq_one A _]
    simp
  · intro i hi
    have := ModuleCat.subsingleton_of_isZero (hK.isZero i hi)
    simp [Module.length_eq_zero]

end koszul

/-! ## 生成 -/

variable [IsNoetherianRing A] (hz : Ideal.span (Set.range z) = maximalIdeal A)
  (hK : IsKoszulResolution z)

include hz in
/-- `z` が `m_A` を生成するとき、`z` に台をもつ完全複体のホモロジーは有限長。`A/(z) = k` は体なので
Artin 環で、`OrdinaryEuler.lean` の `homology_finiteLength_of_isPerfectSupported` が使える。
`homologyLengthSum` を通常の有限和として扱うための条件。 -/
lemma length_homology_ne_top (Q : PerfSupp A z) (i : ℤ) :
    Module.length A (Q.1.homology i) ≠ ⊤ := by
  have := isArtinianRing_quotient_span_of_eq hz
  exact Module.length_ne_top_iff.mpr (homology_finiteLength_of_isPerfectSupported Q.2 i)

include hz hK in
/-- デヴィサージュの一歩：`Q` が `0` 次以下に乗り `H^0(Q) ≠ 0` なら、射 `f : Q → K(z)` で
`Σ ℓ(H(Cone f)) + 1 = Σ ℓ(H(Q))` となるものがある。`H^0(Q)` は有限生成で零でないので `k` への全射
`ε` があり（`exists_surjective_quotient_span`）、`Q → k[0]` を `toSingleOfHomology` で作る。`Q` は
K 射影的なので、擬同型 `K(z) → k[0]` に沿って `f : Q → K(z)` に持ち上がる（`exists_lift_of_quasiIso`）。
`H^0(f)` は `ε` と同型の合成なので全射、したがって `homologyLengthSum_mappingCone` が使える。 -/
lemma exists_mappingCone_step (Q : PerfSupp A z) (htop : ∀ i : ℤ, 0 < i → IsZero (Q.1.X i))
    (h0 : ¬ IsZero (Q.1.homology 0)) :
    ∃ (f : Q.1 ⟶ (koszulPerfSupp z).1),
      homologyLengthSum (CochainComplex.mappingCone f) + 1 = homologyLengthSum Q.1 := by
  have hQd : Q.1.d 0 1 = 0 := (htop 1 one_pos).eq_of_tgt _ _
  have := Q.2.finite 0
  have : Module.Finite A (Q.1.homology 0) := homology_moduleFinite Q.1 0
  obtain ⟨ε, hε⟩ := exists_surjective_quotient_span hz _ h0
  have : ∀ n, Projective (Q.1.X n) := fun n ↦ projective_of_free (Q.2.free n)
  have : Q.1.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact htop
  have : Q.1.IsKProjective := CochainComplex.isKProjective_of_projective Q.1 0
  obtain ⟨f, ⟨H⟩⟩ :=
    exists_lift_of_quasiIso (koszulAugmentation hK) (toSingleOfHomology Q.1 hQd ε)
  have hf0 : HomologicalComplex.homologyMap f 0 = ε ≫ (koszulH0Iso hK).inv := by
    have h1 := toSingleOfHomology_homologyMap Q.1 hQd ε
    have h2 := toSingleOfHomology_homologyMap (koszulComplex z) koszulComplex_d_zero_one
      (koszulH0Iso hK).hom
    have h2' : HomologicalComplex.homologyMap (koszulAugmentation hK) 0 ≫
        (HomologicalComplex.singleObjHomologySelfIso _ 0 _).hom = (koszulH0Iso hK).hom := h2
    rw [← h1, ← H.homologyMap_eq, HomologicalComplex.homologyMap_comp]
    simp only [Category.assoc]
    rw [reassoc_of% h2', Iso.hom_inv_id, Category.comp_id]
  have hsurj : Function.Surjective (HomologicalComplex.homologyMap f 0).hom := by
    rw [hf0]
    intro y
    obtain ⟨x, hx⟩ := hε ((koszulH0Iso hK).hom y)
    exact ⟨x, by simp [hx]⟩
  have hK0 : Module.length A ((koszulComplex z).homology 0) = 1 := by
    rw [(koszulH0Iso hK).toLinearEquiv.length_eq]
    have := isSimpleModule_quotient_span_of_eq hz
    exact Module.length_eq_one A _
  exact ⟨f, homologyLengthSum_mappingCone f htop (fun i hi ↦ hK.isZero i hi) hsurj hK0
    (length_homology_ne_top hz Q) Q.2.bounded⟩

include hz hK in
/-- **`K₀^{m}(A)` は `[K(z)]` で生成される**：`z` に台をもつ完全複体 `Q` について、整数 `m` があって
`[Q] = m · [K(z)]`。

証明は `n = homologyLengthSum Q` についての強い帰納法。内側の主張 `norm` は「`Q` が `[-w, 0]` に乗る
なら結論が成り立つ」で、`w` についての帰納法で示す：`H^0(Q) ≠ 0` なら `exists_mappingCone_step` で
`f : Q → K(z)` をとり、錐に外側の帰納法の仮定を使って `[Q] = [K(z)] - [Cone f] = (1 - m)[K(z)]`。
`H^0(Q) = 0` なら `exists_homotopyEquiv_truncate` で `[-w, -1]` に乗るホモトピー同値な `Q'` に移り、
`w = 0` なら `Q'` は零複体で `[Q] = 0`、そうでなければ `Q'⟦-1⟧` は `[-(w-1), 0]` に乗るので内側の
帰納法の仮定が使え、`[Q] = [Q'] = -[Q'⟦-1⟧]`。一般の `Q` は、`[a, b]` に乗るとき `Q⟦b⟧` に `norm` を
適用し、`[Q⟦b⟧] = (-1)^b [Q]` で戻す。 -/
theorem K0.exists_eq_zsmul_koszul (Q : PerfSupp A z) :
    ∃ m : ℤ, K0.mk Q = m • K0.mk (koszulPerfSupp z) := by
  suffices H : ∀ n (Q : PerfSupp A z), homologyLengthSum Q.1 = n →
      ∃ m : ℤ, K0.mk Q = m • K0.mk (koszulPerfSupp z) from H _ Q rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  -- 最上段が `0` 次、最下段が `-w` 次以上の場合
  have norm : ∀ (w : ℕ) (Q : PerfSupp A z), homologyLengthSum Q.1 = n →
      (∀ i : ℤ, 0 < i → IsZero (Q.1.X i)) → (∀ i : ℤ, i < -(w : ℤ) → IsZero (Q.1.X i)) →
      ∃ m : ℤ, K0.mk Q = m • K0.mk (koszulPerfSupp z) := by
    intro w
    induction w with
    | zero => ?_
    | succ w ihw => ?_
    all_goals
      intro Q hn htop hbot
      by_cases h0 : IsZero (Q.1.homology 0)
      swap
      · -- 錐による一歩
        obtain ⟨f, hlen⟩ := exists_mappingCone_step hz hK Q htop h0
        have hc := Q.2.mappingCone f (koszulPerfSupp z).2
        obtain ⟨m, hm⟩ := ih (homologyLengthSum (CochainComplex.mappingCone f)) (by omega)
          ⟨_, hc⟩ rfl
        have hcone := K0.mk_cone Q (koszulPerfSupp z) f hc
        refine ⟨1 - m, ?_⟩
        rw [sub_smul, one_smul, ← hm, hcone, sub_sub_cancel]
      -- 最上段の切り詰め
      obtain ⟨Q', hfree, hfin, htop', hbot', ⟨E⟩⟩ :=
        exists_homotopyEquiv_truncate Q.1 Q.2.free Q.2.finite htop h0
      have hQ' : IsPerfectSupported z Q' :=
        { bounded := by
            obtain ⟨a, b, hab⟩ := Q.2.bounded
            refine ⟨min a (-1), 0, fun i hi ↦ ?_⟩
            rcases hi with hi | hi
            · exact hbot' i (by omega) (hab i (Or.inl (by omega)))
            · exact htop' i (by omega)
          free := hfree
          finite := hfin
          supported := Q.2.supported.of_homotopyEquiv E.symm }
      have hmk : K0.mk Q = K0.mk ⟨Q', hQ'⟩ := (K0.mk_eq_of_homotopyEquiv ⟨Q', hQ'⟩ Q E).symm
      have hlen : homologyLengthSum Q' = n := by
        rw [homologyLengthSum_eq_of_homotopyEquiv E, hn]
    -- `w = 0`：`Q'` は零
    · refine ⟨0, ?_⟩
      rw [zero_smul, hmk]
      refine K0.mk_eq_zero_of_isZero _ (isZero_of_isZero_X fun i ↦ ?_)
      rcases lt_or_ge (-1) i with hi | hi
      · exact htop' i hi
      · exact hbot' i hi (hbot i (by omega))
    -- `w + 1`：`Q'⟦-1⟧` に帰納法の仮定を使う
    · obtain ⟨m, hm⟩ := ihw ⟨Q'⟦(-1 : ℤ)⟧, hQ'.shift (-1)⟩
        (by rw [homologyLengthSum_shift, hlen])
        (fun i hi ↦ htop' (i + -1) (by omega))
        (fun i hi ↦ hbot' (i + -1) (by omega) (hbot _ (by push_cast at hi ⊢; omega)))
      rw [K0.mk_shift ⟨Q', hQ'⟩ (-1), Int.negOnePow_neg, Int.negOnePow_one, Units.val_neg,
        Units.val_one, neg_smul, one_smul] at hm
      refine ⟨-m, ?_⟩
      rw [hmk, neg_smul, ← hm, neg_neg]
  -- 一般の `Q`：シフトで最上段を `0` 次にそろえる
  intro Q hn
  obtain ⟨a, b, hab⟩ := Q.2.bounded
  obtain ⟨m, hm⟩ := norm (b - a).toNat ⟨Q.1⟦b⟧, Q.2.shift b⟩
    (by rw [homologyLengthSum_shift, hn])
    (fun i hi ↦ hab (i + b) (by omega))
    (fun i hi ↦ hab (i + b) (by omega))
  rw [K0.mk_shift] at hm
  refine ⟨((b.negOnePow : ℤˣ) : ℤ) * m, ?_⟩
  rw [mul_smul, ← hm, ← mul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]

include hz hK in
/-- `K₀^{m}(A)` からの二つの準同型 `φ`、`ψ` が `[K(z)]` で一致すれば等しい。任意の類が `[K(z)]` の
整数倍だから。Lemma 3.5b（`Paper/Lemma3_5/`）で、`χ_T(P ⊗ T)` と `rank_A T · χ_A(P)` のような二つの
加法的関数の一致を `P = K(z)` の場合に帰着させるのに使う。 -/
theorem K0.hom_ext_koszul {β : Type*} [AddCommGroup β] {φ ψ : K0Supported A z →+ β}
    (h : φ (K0.mk (koszulPerfSupp z)) = ψ (K0.mk (koszulPerfSupp z))) : φ = ψ :=
  K0.hom_ext fun Q ↦ by
    obtain ⟨m, hm⟩ := K0.exists_eq_zsmul_koszul hz hK Q
    rw [hm, map_zsmul, map_zsmul, h]

end SerrePositivity
