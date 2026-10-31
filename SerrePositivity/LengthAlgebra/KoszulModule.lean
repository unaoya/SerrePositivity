module

public import SerrePositivity.LengthAlgebra.Core
public import SerrePositivity.HomologicalAlgebra.KoszulScalarControl
public import SerrePositivity.CommutativeAlgebra.AlgebraMapCokernel
public import SerrePositivity.PerfectComplex.Free.Euler
public import SerrePositivity.LengthAlgebra.Cone
public import SerrePositivity.HomologicalAlgebra.KoszulModuleBounds
public import SerrePositivity.HomologicalAlgebra.KoszulIdealAction
public import SerrePositivity.HomologicalAlgebra.KoszulRestriction
public import SerrePositivity.LengthAlgebra.Normalized
public import SerrePositivity.CommutativeAlgebra.KoszulResolution

/-! # 代数を係数とする Koszul ホモロジーの長さ

## 概要

単射な代数写像の Koszul ホモロジーの長さの誤差を余核を係数とする隣接次数の長さで抑え、最後の元がホモロジー上で零に作用する Koszul 複体の Euler 評価、余核の Euler 消去による比較、高次の長さが消えるときの零次への還元、係数制限との両立、列の生成イデアルを大きくしたときの第零 Koszul ホモロジーの長さの単調性を与える。

## 方針

長さの加法性に必要な冪ねじれ性は列のイデアルへの台の条件から供給し、Euler の相殺は全列のホモロジー長の有限性から導く。

## 規約

係数代数の Noether 性や有限生成性は要求しない。

## 使われ方

CLMST の Koszul の長さの比較と巡回評価。
-/

@[expose] public noncomputable section

universe u

section KoszulCokernelBoundsPart

namespace SerrePositivity
open CategoryTheory
variable {S : Type u} [CommRing S] {J : Ideal S} (lam : NormalizedLength S J)

/-- 係数加群に依存せず、台の条件から Koszul ホモロジーの冪ねじれ性を供給する。 -/
theorem isPowTorsion_koszulModuleHomology (hfg : J.FG) {e : ℕ} (z : Fin e → S)
    (hJ : J ≤ (Ideal.span (Set.range z)).radical) (M : ModuleCat.{u} S) (q : ℤ) :
    IsPowTorsion J (((koszulModuleFunctor z).obj M).homology q) :=
  supported_homology_isPowTorsion hfg hJ
    (isSupported_koszulComplexOn z ((HomologicalComplex.single _ (.up ℤ) 0).obj M)) q

/-- 比較する二つの Koszul ホモロジーの長さを、余核の長さで両方向から抑える。
値は ℝ≥0∞。Noether 性、有限長、余核の長さ零を要求しない。 -/
theorem lambdaKoszul_algebraMap_cokernel_bounds
    (C : Type u) [CommRing C] [Algebra S C]
    (hinj : Function.Injective (algebraMap S C)) (hfg : J.FG)
    {e : ℕ} (z : Fin e → S) (hJ : J ≤ (Ideal.span (Set.range z)).radical) (q : ℤ) :
    (lam.len (((koszulModuleFunctor z).obj (ModuleCat.of S C)).homology q) ≤
      lam.len (((koszulModuleFunctor z).obj (ModuleCat.of S S)).homology q) +
      lam.len (((koszulModuleFunctor z).obj
        (ModuleCat.of S (AlgebraMapCokernel S C))).homology q)) ∧
    (lam.len (((koszulModuleFunctor z).obj (ModuleCat.of S S)).homology q) ≤
      lam.len (((koszulModuleFunctor z).obj
        (ModuleCat.of S (AlgebraMapCokernel S C))).homology (q - 1)) +
      lam.len (((koszulModuleFunctor z).obj (ModuleCat.of S C)).homology q)) := by
  let sc := (algebraMapCokernelShortComplex S C).map (koszulModuleFunctor z)
  have hs := koszulModuleFunctor_shortExact z (algebraMapCokernelShortComplex S C)
    (algebraMapCokernelShortComplex_shortExact S C hinj)
  have ht₁ := isPowTorsion_koszulModuleHomology hfg z hJ (ModuleCat.of S S) q
  have ht₂ := isPowTorsion_koszulModuleHomology hfg z hJ (ModuleCat.of S C) q
  have ht₃ := isPowTorsion_koszulModuleHomology hfg z hJ
    (ModuleCat.of S (AlgebraMapCokernel S C)) q
  have htprev := isPowTorsion_koszulModuleHomology hfg z hJ
    (ModuleCat.of S (AlgebraMapCokernel S C)) (q - 1)
  exact ⟨lambdaHomology_shortExact_le lam sc hs q ht₁ ht₂ ht₃,
    lambdaHomology_shortExact_left_le lam sc hs q htprev ht₁ ht₂⟩

/-- 余核の隣接する二次数の長さが零なら、比較する Koszul ホモロジーの長さは一致。 -/
theorem lambdaKoszul_algebraMap_eq_of_cokernel_length_zero
    (C : Type u) [CommRing C] [Algebra S C]
    (hinj : Function.Injective (algebraMap S C)) (hfg : J.FG)
    {e : ℕ} (z : Fin e → S) (hJ : J ≤ (Ideal.span (Set.range z)).radical) (q : ℤ)
    (hprev : lam.len (((koszulModuleFunctor z).obj
      (ModuleCat.of S (AlgebraMapCokernel S C))).homology (q - 1)) = 0)
    (hcurrent : lam.len (((koszulModuleFunctor z).obj
      (ModuleCat.of S (AlgebraMapCokernel S C))).homology q) = 0) :
    lam.len (((koszulModuleFunctor z).obj (ModuleCat.of S S)).homology q) =
      lam.len (((koszulModuleFunctor z).obj (ModuleCat.of S C)).homology q) := by
  have hb := lambdaKoszul_algebraMap_cokernel_bounds lam C hinj hfg z hJ q
  apply le_antisymm
  · simpa only [hprev, zero_add] using hb.2
  · simpa only [hcurrent, add_zero] using hb.1

/-- 比較先の同次数と比較元の次次数が有限なら、余核の Koszul 長も有限。 -/
theorem lambdaKoszul_algebraMap_cokernel_ne_top
    (C : Type u) [CommRing C] [Algebra S C]
    (hinj : Function.Injective (algebraMap S C)) (hfg : J.FG)
    {e : ℕ} (z : Fin e → S) (hJ : J ≤ (Ideal.span (Set.range z)).radical) (q : ℤ)
    (hC : lam.len (((koszulModuleFunctor z).obj (ModuleCat.of S C)).homology q) ≠ ⊤)
    (hSnext : lam.len (((koszulModuleFunctor z).obj (ModuleCat.of S S)).homology (q + 1)) ≠ ⊤) :
    lam.len (((koszulModuleFunctor z).obj
      (ModuleCat.of S (AlgebraMapCokernel S C))).homology q) ≠ ⊤ := by
  let sc := (algebraMapCokernelShortComplex S C).map (koszulModuleFunctor z)
  have hs := koszulModuleFunctor_shortExact z (algebraMapCokernelShortComplex S C)
    (algebraMapCokernelShortComplex_shortExact S C hinj)
  exact lambdaHomology_shortExact_right_ne_top lam sc hs q
    (isPowTorsion_koszulModuleHomology hfg z hJ (ModuleCat.of S C) q)
    (isPowTorsion_koszulModuleHomology hfg z hJ
      (ModuleCat.of S (AlgebraMapCokernel S C)) q)
    (isPowTorsion_koszulModuleHomology hfg z hJ (ModuleCat.of S S) (q + 1)) hC hSnext

end SerrePositivity

end KoszulCokernelBoundsPart

section KoszulErrorEulerPart

namespace SerrePositivity
open CategoryTheory Limits
variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)

/-- 最後の元が前の列のホモロジー上で零なら、全列の負次数の有限性から
前の列の全次数のホモロジー長の有限性が従う。係数加群の有限生成性は不要。 -/
theorem lambdaHomology_koszulModule_init_ne_top_of_last_homology_action_zero
    {e : ℕ} (z : Fin (e + 1) → R) (M : ModuleCat.{u} R)
    (hz : ∀ q, HomologicalComplex.homologyMap
      (smulId (z (Fin.last e)) ((koszulModuleFunctor (Fin.init z)).obj M)) q = 0)
    (tFull : ∀ q, IsPowTorsion J (((koszulModuleFunctor z).obj M).homology q))
    (lNegative : ∀ q : ℤ, q < 0 →
      lam.len (((koszulModuleFunctor z).obj M).homology q) ≠ ⊤) :
    ∀ q : ℤ, lam.len (((koszulModuleFunctor (Fin.init z)).obj M).homology q) ≠ ⊤ := by
  let P := (koszulModuleFunctor (Fin.init z)).obj M
  let f := smulId (z (Fin.last e)) P
  intro q
  by_cases hq : 0 < q
  · let := ModuleCat.subsingleton_of_isZero (isZero_homology_of_isZero_X P q
      (koszulModuleFunctor_isZero_X_of_pos (Fin.init z) M q hq))
    rw [lam.len_eq_zero_of_subsingleton]
    exact ENNReal.zero_ne_top
  · exact ne_top_of_le_ne_top (lNegative (q - 1) (by omega))
      (lambdaHomology_le_cone_prev_of_homologyMap_eq_zero lam f q (hz q) (tFull (q - 1)))

/-- 最後の元が前の列のホモロジー上で零なら、負次数の有限性だけから
全列の全整数次数のホモロジー長が有限となる。零次数も錐の完全列から導く。 -/
theorem lambdaHomology_koszulModule_ne_top_of_last_homology_action_zero
    {e : ℕ} (z : Fin (e + 1) → R) (M : ModuleCat.{u} R)
    (hz : ∀ q, HomologicalComplex.homologyMap
      (smulId (z (Fin.last e)) ((koszulModuleFunctor (Fin.init z)).obj M)) q = 0)
    (tFull : ∀ q, IsPowTorsion J (((koszulModuleFunctor z).obj M).homology q))
    (lNegative : ∀ q : ℤ, q < 0 →
      lam.len (((koszulModuleFunctor z).obj M).homology q) ≠ ⊤) :
    ∀ q : ℤ, lam.len (((koszulModuleFunctor z).obj M).homology q) ≠ ⊤ := by
  let P := (koszulModuleFunctor (Fin.init z)).obj M
  let f := smulId (z (Fin.last e)) P
  have tP (q : ℤ) : IsPowTorsion J (P.homology q) :=
    isPowTorsion_of_cone_of_homologyMap_eq_zero f q (hz q) (tFull q)
  have lP := lambdaHomology_koszulModule_init_ne_top_of_last_homology_action_zero
    lam z M hz tFull lNegative
  intro q
  change lam.len ((Cone.cone f).homology q) ≠ ⊤
  rw [(lambdaHomology_cone_of_homologyMap_eq_zero lam f hz q (tP q) (tP (q + 1))).2]
  exact ENNReal.add_ne_top.mpr ⟨lP q, lP (q + 1)⟩

/-- 最後の元が前の列と係数の零化元の生成イデアルに属すれば、
負次数の有限性から全次数のホモロジー長の有限性が従う。 -/
theorem lambdaHomology_koszulModule_ne_top_of_last_mem_span_sup
    {e : ℕ} (z : Fin (e + 1) → R) (M : ModuleCat.{u} R) (a : R)
    (ha : ∀ m : M, a • m = 0)
    (hz : z (Fin.last e) ∈ Ideal.span (Set.range (Fin.init z)) ⊔ Ideal.span {a})
    (tFull : ∀ q, IsPowTorsion J (((koszulModuleFunctor z).obj M).homology q))
    (lNegative : ∀ q : ℤ, q < 0 →
      lam.len (((koszulModuleFunctor z).obj M).homology q) ≠ ⊤) :
    ∀ q : ℤ, lam.len (((koszulModuleFunctor z).obj M).homology q) ≠ ⊤ :=
  lambdaHomology_koszulModule_ne_top_of_last_homology_action_zero lam z M
    (koszul_last_homologyMap_eq_zero_of_mem_span_sup z M a ha hz) tFull lNegative

/-- 最後の元が前の列のホモロジー上で零なら、負次数の全列の有限性だけでEuler評価零。
前の列の有限性・冪ねじれ性と全列の零次数の有限性を、錐の完全列から導く。 -/
theorem lambdaEuler_koszulModule_eq_zero_of_last_homology_action_zero
    {e : ℕ} (z : Fin (e + 1) → R) (M : ModuleCat.{u} R)
    (hz : ∀ q, HomologicalComplex.homologyMap
      (smulId (z (Fin.last e)) ((koszulModuleFunctor (Fin.init z)).obj M)) q = 0)
    (tFull : ∀ q, IsPowTorsion J (((koszulModuleFunctor z).obj M).homology q))
    (lNegative : ∀ q : ℤ, q < 0 →
      lam.len (((koszulModuleFunctor z).obj M).homology q) ≠ ⊤) :
    lambdaEuler lam ((koszulModuleFunctor z).obj M) = 0 := by
  let P := (koszulModuleFunctor (Fin.init z)).obj M
  let f := smulId (z (Fin.last e)) P
  have tP (q : ℤ) : IsPowTorsion J (P.homology q) :=
    isPowTorsion_of_cone_of_homologyMap_eq_zero f q (hz q) (tFull q)
  have lFull := lambdaHomology_koszulModule_ne_top_of_last_homology_action_zero
    lam z M hz tFull lNegative
  exact lambdaEuler_self_cone_eq_zero_of_homologyMap_eq_zero lam f hz
    (koszulModuleFunctor_bounded (Fin.init z) M) (koszulModuleFunctor_bounded z M)
    tP tFull lFull

/-- 最後の元が前の列と係数の零化元の生成イデアルに属すれば、Euler評価は零。
ホモロジー上の零作用は所属条件から証明し、未知の条件として渡さない。 -/
theorem lambdaEuler_koszulModule_eq_zero_of_last_mem_span_sup
    {e : ℕ} (z : Fin (e + 1) → R) (M : ModuleCat.{u} R) (a : R)
    (ha : ∀ m : M, a • m = 0)
    (hz : z (Fin.last e) ∈ Ideal.span (Set.range (Fin.init z)) ⊔ Ideal.span {a})
    (tFull : ∀ q, IsPowTorsion J (((koszulModuleFunctor z).obj M).homology q))
    (lNegative : ∀ q : ℤ, q < 0 →
      lam.len (((koszulModuleFunctor z).obj M).homology q) ≠ ⊤) :
    lambdaEuler lam ((koszulModuleFunctor z).obj M) = 0 :=
  lambdaEuler_koszulModule_eq_zero_of_last_homology_action_zero lam z M
    (koszul_last_homologyMap_eq_zero_of_mem_span_sup z M a ha hz) tFull lNegative

end SerrePositivity

end KoszulErrorEulerPart

section KoszulEulerComparisonPart

namespace SerrePositivity
open CategoryTheory
variable {S : Type u} [CommRing S] {J : Ideal S} (lam : NormalizedLength S J)

/-- 余核の負次数の有限性と最後の元の所属から、比較先の零次数を含む全長さも有限になる。 -/
theorem lambdaKoszul_algebraMap_target_ne_top_of_last_mem_span_sup
    (C : Type u) [CommRing C] [Algebra S C]
    (hinj : Function.Injective (algebraMap S C)) (hfg : J.FG)
    {e : ℕ} (z : Fin (e + 1) → S) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
    (a : S) (ha : ∀ m : AlgebraMapCokernel S C, a • m = 0)
    (hz : z (Fin.last e) ∈ Ideal.span (Set.range (Fin.init z)) ⊔ Ideal.span {a})
    (lS : ∀ q, lam.len (((koszulModuleFunctor z).obj (ModuleCat.of S S)).homology q) ≠ ⊤)
    (lNegative : ∀ q : ℤ, q < 0 → lam.len (((koszulModuleFunctor z).obj
      (ModuleCat.of S (AlgebraMapCokernel S C))).homology q) ≠ ⊤)
    (q : ℤ) :
    lam.len (((koszulModuleFunctor z).obj (ModuleCat.of S C)).homology q) ≠ ⊤ := by
  have lQ := lambdaHomology_koszulModule_ne_top_of_last_mem_span_sup lam z
    (ModuleCat.of S (AlgebraMapCokernel S C)) a ha hz
    (isPowTorsion_koszulModuleHomology hfg z hJ _) lNegative
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨lS q, lQ q⟩)
    (lambdaKoszul_algebraMap_cokernel_bounds lam C hinj hfg z hJ q).1

/-- 比較元と余核の全長さが有限で、余核の Euler 評価が零なら、二つの Euler 評価は一致する。 -/
theorem lambdaKoszul_algebraMap_euler_eq_of_cokernel_euler_zero
    (C : Type u) [CommRing C] [Algebra S C]
    (hinj : Function.Injective (algebraMap S C)) (hfg : J.FG)
    {e : ℕ} (z : Fin e → S) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
    (lS : ∀ q, lam.len (((koszulModuleFunctor z).obj (ModuleCat.of S S)).homology q) ≠ ⊤)
    (lQ : ∀ q, lam.len (((koszulModuleFunctor z).obj
      (ModuleCat.of S (AlgebraMapCokernel S C))).homology q) ≠ ⊤)
    (hQ : lambdaEuler lam ((koszulModuleFunctor z).obj
      (ModuleCat.of S (AlgebraMapCokernel S C))) = 0) :
    lambdaEuler lam ((koszulModuleFunctor z).obj (ModuleCat.of S C)) =
      lambdaEuler lam ((koszulModuleFunctor z).obj (ModuleCat.of S S)) := by
  let sc := (algebraMapCokernelShortComplex S C).map (koszulModuleFunctor z)
  have hs := koszulModuleFunctor_shortExact z (algebraMapCokernelShortComplex S C)
    (algebraMapCokernelShortComplex_shortExact S C hinj)
  have tS := isPowTorsion_koszulModuleHomology hfg z hJ (ModuleCat.of S S)
  have tC := isPowTorsion_koszulModuleHomology hfg z hJ (ModuleCat.of S C)
  have tQ := isPowTorsion_koszulModuleHomology hfg z hJ
    (ModuleCat.of S (AlgebraMapCokernel S C))
  have lC (q : ℤ) : lam.len (sc.X₂.homology q) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨lS q, lQ q⟩)
      (lambdaHomology_shortExact_le lam sc hs q (tS q) (tC q) (tQ q))
  have he := lambdaEuler_shortExact lam sc hs
    (koszulModuleFunctor_bounded z (ModuleCat.of S C))
    (koszulModuleFunctor_bounded z (ModuleCat.of S (AlgebraMapCokernel S C)))
    tS tC tQ lS lC lQ
  change lambdaEuler lam ((koszulModuleFunctor z).obj (ModuleCat.of S C)) =
    lambdaEuler lam ((koszulModuleFunctor z).obj (ModuleCat.of S S)) +
      lambdaEuler lam ((koszulModuleFunctor z).obj
        (ModuleCat.of S (AlgebraMapCokernel S C))) at he
  simpa only [hQ, add_zero] using he

end SerrePositivity

end KoszulEulerComparisonPart

section KoszulEulerZeroPart

open scoped ENNReal
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)

/-- 零次以外のホモロジーの長さが零なら、Euler 評価は零次の長さの実数値。
有界性や長さの有限性を要求しない。 -/
theorem lambdaEuler_eq_zero_homology_length
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hzero : ∀ q : ℤ, q ≠ 0 → lam.len (P.homology q) = 0) :
    lambdaEuler lam P = (lam.len (P.homology 0)).toReal := by
  unfold lambdaEuler
  rw [finsum_eq_single _ 0 (fun q hq ↦ by simp [hzero q hq])]
  simp

/-- Koszul ホモロジーの負次数の長さが全て零なら、Euler 評価は零次の長さ。
正次数は複体の項の範囲から消滅する。 -/
theorem lambdaEuler_koszulModule_eq_zero_homology_length
    {r : ℕ} (z : Fin r → R) (M : ModuleCat.{u} R)
    (hnegative : ∀ q : ℤ, q < 0 →
      lam.len (((koszulModuleFunctor z).obj M).homology q) = 0) :
    lambdaEuler lam ((koszulModuleFunctor z).obj M) =
      (lam.len (((koszulModuleFunctor z).obj M).homology 0)).toReal := by
  apply lambdaEuler_eq_zero_homology_length
  intro q hq
  rcases lt_or_gt_of_ne hq with hq | hq
  · exact hnegative q hq
  · have hz := isZero_homology_of_isZero_X ((koszulModuleFunctor z).obj M) q
      (koszulModuleFunctor_isZero_X_of_pos z M q hq)
    let : Subsingleton (((koszulModuleFunctor z).obj M).homology q) :=
      ModuleCat.subsingleton_of_isZero hz
    exact lam.len_eq_zero_of_subsingleton _

/-- 列に末尾の元を追加する係数加群の Koszul 構成は、スカラー乗法の錐。 -/
theorem koszulModuleFunctor_snoc_eq {r : ℕ} (z : Fin r → R) (a : R)
    (M : ModuleCat.{u} R) :
    (koszulModuleFunctor (Fin.snoc z a)).obj M =
      Cone.cone (smulId a ((koszulModuleFunctor z).obj M)) := by
  simp only [koszulModuleFunctor, koszulFunctor, Fin.init_snoc, Fin.snoc_last,
    Functor.comp_obj]
  rfl

/-- 末尾だけを正冪に替える Koszul Euler 評価は、その指数倍。
全正冪のホモロジーの冪ねじれ性と長さの有限性を明示的に受け取る。 -/
theorem lambdaEuler_koszulModule_last_pow {r : ℕ} (z : Fin r → R) (a : R)
    (M : ModuleCat.{u} R)
    (ht : ∀ n : ℕ, 0 < n → ∀ q,
      IsPowTorsion J (((koszulModuleFunctor (Fin.snoc z (a ^ n))).obj M).homology q))
    (hl : ∀ n : ℕ, 0 < n → ∀ q,
      lam.len (((koszulModuleFunctor (Fin.snoc z (a ^ n))).obj M).homology q) ≠ ⊤)
    (k : ℕ) (hk : 0 < k) :
    lambdaEuler lam ((koszulModuleFunctor (Fin.snoc z (a ^ k))).obj M) =
      (k : ℝ) * lambdaEuler lam ((koszulModuleFunctor (Fin.snoc z a)).obj M) := by
  rw [koszulModuleFunctor_snoc_eq, koszulModuleFunctor_snoc_eq]
  apply lambdaEuler_scalarCone_pow lam ((koszulModuleFunctor z).obj M) a _ _ _ k hk
  · intro n hn
    have hb := koszulModuleFunctor_bounded (Fin.snoc z (a ^ n)) M
    rwa [koszulModuleFunctor_snoc_eq] at hb
  · intro n hn
    have ht' := ht n hn
    rwa [koszulModuleFunctor_snoc_eq] at ht'
  · intro n hn
    have hl' := hl n hn
    rwa [koszulModuleFunctor_snoc_eq] at hl'

/-- 負次数の長さ消滅と全次数の有限性のもとで、末尾の正冪の零次長さは指数倍。
実数 Euler 評価から拡張非負実数値へ戻す際の有限性を明示する。 -/
theorem length_koszulModule_zero_last_pow {r : ℕ} (z : Fin r → R) (a : R)
    (M : ModuleCat.{u} R)
    (ht : ∀ n : ℕ, 0 < n → ∀ q,
      IsPowTorsion J (((koszulModuleFunctor (Fin.snoc z (a ^ n))).obj M).homology q))
    (hl : ∀ n : ℕ, 0 < n → ∀ q,
      lam.len (((koszulModuleFunctor (Fin.snoc z (a ^ n))).obj M).homology q) ≠ ⊤)
    (hnegative : ∀ n : ℕ, 0 < n → ∀ q : ℤ, q < 0 →
      lam.len (((koszulModuleFunctor (Fin.snoc z (a ^ n))).obj M).homology q) = 0)
    (k : ℕ) (hk : 0 < k) :
    lam.len (((koszulModuleFunctor (Fin.snoc z (a ^ k))).obj M).homology 0) =
      (k : ℝ≥0∞) * lam.len (((koszulModuleFunctor (Fin.snoc z a)).obj M).homology 0) := by
  have he := lambdaEuler_koszulModule_last_pow lam z a M ht hl k hk
  have hn₁ := hnegative 1 one_pos
  rw [pow_one] at hn₁
  rw [lambdaEuler_koszulModule_eq_zero_homology_length lam _ M (hnegative k hk),
    lambdaEuler_koszulModule_eq_zero_homology_length lam _ M hn₁] at he
  have hf₁ := hl 1 one_pos 0
  rw [pow_one] at hf₁
  apply (ENNReal.toReal_eq_toReal_iff' (hl k hk 0)
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top k) hf₁)).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
  exact he

end SerrePositivity

end KoszulEulerZeroPart

section KoszulRestrictionPart

namespace SerrePositivity
open CategoryTheory
set_option backward.isDefEq.respectTransparency false

/-- 代数作用から作った係数加群と、環準同型による係数制限の作用を明示的に比較。 -/
def koszulModuleAlgebraHomologyIso
    {S C : Type u} [CommRing S] [CommRing C] [Algebra S C]
    {r : ℕ} (z : Fin r → S) (q : ℤ) :
    ((koszulModuleFunctor z).obj (ModuleCat.of S C)).homology q ≅
      (ModuleCat.restrictScalars (algebraMap S C)).obj
        ((koszulComplex (algebraMap S C ∘ z)).homology q) := by
  let ec : ModuleCat.of S C ≅
      (ModuleCat.restrictScalars (algebraMap S C)).obj (ModuleCat.of C C) :=
    LinearEquiv.toModuleIso
      (X₁ := ModuleCat.of S C)
      (X₂ := (ModuleCat.restrictScalars (algebraMap S C)).obj (ModuleCat.of C C))
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun a x ↦ by
          change a • x = algebraMap S C a * x
          exact Algebra.smul_def a x }
  exact (HomologicalComplex.homologyFunctor _ _ q).mapIso
    ((koszulModuleFunctor z).mapIso ec) ≪≫
    koszulModuleHomologyIso (algebraMap S C) z q

/-- 係数加群の Koszul ホモロジーを二段の係数制限で測る長さは、
係数代数上の Koszul ホモロジーを直接測る長さと一致する。 -/
theorem length_comap_koszulModuleHomology
    {R S C : Type u} [CommRing R] [CommRing S] [CommRing C]
    [Algebra R S] [Algebra S C] [Algebra R C] [IsScalarTower R S C]
    {J : Ideal R} (lam : NormalizedLength R J) (K : Ideal S)
    (hK : J.map (algebraMap R S) ≤ K) {r : ℕ} (z : Fin r → S) (q : ℤ) :
    (lam.comap (algebraMap R S) K hK).len
      (((koszulModuleFunctor z).obj (ModuleCat.of S C)).homology q) =
    (let _ := Module.compHom ((koszulComplex (algebraMap S C ∘ z)).homology q)
      (algebraMap R C)
     lam.len ((koszulComplex (algebraMap S C ∘ z)).homology q)) := by
  let β := algebraMap S C
  let φ := algebraMap R S
  let X := ((koszulModuleFunctor z).obj (ModuleCat.of S C)).homology q
  let H := (koszulComplex (β ∘ z)).homology q
  let e : (ModuleCat.restrictScalars φ).obj X ≅
      (ModuleCat.restrictScalars (algebraMap R C)).obj H :=
    (ModuleCat.restrictScalars φ).mapIso (koszulModuleAlgebraHomologyIso z q) ≪≫
      (ModuleCat.restrictScalarsComp'App φ β (algebraMap R C)
        (IsScalarTower.algebraMap_eq R S C) H).symm
  let := Module.compHom X φ
  let := Module.compHom H (algebraMap R C)
  exact lam.len_congr _ _ e.toLinearEquiv

end SerrePositivity

end KoszulRestrictionPart

section KoszulZeroMonotonicityPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.LengthAlgebra
open CategoryTheory

variable {S C : Type u} [CommRing S] [CommRing C] [Algebra S C]

/-- 代数を係数とする第零 Koszul ホモロジーを、係数代数の商を底環へ制限した加群と同定する。
環準同型からの作用と通常の代数作用の違いは、既存の Koszul 制限同型で処理する。 -/
def koszulModuleHomologyZeroQuotientIso {r : ℕ} (z : Fin r → S) :
    ((koszulModuleFunctor z).obj (ModuleCat.of S C)).homology 0 ≅
      (ModuleCat.restrictScalars (algebraMap S C)).obj
        (ModuleCat.of C (C ⧸ Ideal.span (Set.range (algebraMap S C ∘ z)))) :=
  koszulModuleAlgebraHomologyIso z 0 ≪≫
    (ModuleCat.restrictScalars (algebraMap S C)).mapIso
      (LinearEquiv.toModuleIso
        (X₁ := (koszulComplex (algebraMap S C ∘ z)).homology 0)
        (X₂ := ModuleCat.of C (C ⧸ Ideal.span (Set.range (algebraMap S C ∘ z))))
        (koszulComplex_homology_zero_equiv (algebraMap S C ∘ z)).some)

/-- 生成イデアルの包含から、代数係数の第零 Koszul ホモロジー間の全射を作る。
商写像を C 線形に作り、S へ制限して両側の Koszul モデルへ戻す。 -/
theorem exists_surjective_koszulModuleHomology_zero_of_span_le
    {r e : ℕ} (w : Fin r → S) (z : Fin e → S)
    (hspan : Ideal.span (Set.range w) ≤ Ideal.span (Set.range z)) :
    ∃ f : ((koszulModuleFunctor w).obj (ModuleCat.of S C)).homology 0 →ₗ[S]
      ((koszulModuleFunctor z).obj (ModuleCat.of S C)).homology 0,
      Function.Surjective f := by
  have hC : Ideal.span (Set.range (algebraMap S C ∘ w)) ≤
      Ideal.span (Set.range (algebraMap S C ∘ z)) := by
    simpa only [Ideal.map_span, ← Set.range_comp] using
      Ideal.map_mono (f := algebraMap S C) hspan
  let qw := C ⧸ Ideal.span (Set.range (algebraMap S C ∘ w))
  let qz := C ⧸ Ideal.span (Set.range (algebraMap S C ∘ z))
  let q : (ModuleCat.restrictScalars (algebraMap S C)).obj (ModuleCat.of C qw) ⟶
      (ModuleCat.restrictScalars (algebraMap S C)).obj (ModuleCat.of C qz) :=
    (ModuleCat.restrictScalars (algebraMap S C)).map
      (ModuleCat.ofHom (Ideal.Quotient.factorₐ C hC).toLinearMap)
  have hq : Function.Surjective q.hom := Ideal.Quotient.factor_surjective hC
  let ew := (koszulModuleHomologyZeroQuotientIso (C := C) w).toLinearEquiv
  let ez := (koszulModuleHomologyZeroQuotientIso (C := C) z).toLinearEquiv
  refine ⟨ez.symm.toLinearMap ∘ₗ q.hom ∘ₗ ew.toLinearMap, ?_⟩
  exact ez.symm.surjective.comp (hq.comp ew.surjective)

/-- 列の生成イデアルが大きくなると、第零 Koszul ホモロジーの正規化長さは減少する。
測定イデアルの有限生成性と元の列への台の条件から、全射の源の冪ねじれ性だけを供給する。 -/
theorem lambdaKoszul_homology_zero_le_of_span_le {J : Ideal S}
    (lam : NormalizedLength S J) (C : Type u) [CommRing C] [Algebra S C]
    (hfg : J.FG) {r e : ℕ}
    (w : Fin r → S) (z : Fin e → S)
    (hJ : J ≤ (Ideal.span (Set.range w)).radical)
    (hspan : Ideal.span (Set.range w) ≤ Ideal.span (Set.range z)) :
    lam.len (((koszulModuleFunctor z).obj (ModuleCat.of S C)).homology 0) ≤
      lam.len (((koszulModuleFunctor w).obj (ModuleCat.of S C)).homology 0) := by
  obtain ⟨f, hf⟩ := exists_surjective_koszulModuleHomology_zero_of_span_le (C := C) w z hspan
  exact lam.len_le_of_surjective f hf
    (isPowTorsion_koszulModuleHomology hfg w hJ (ModuleCat.of S C) 0)

/-- 二段の係数制限で測る第零 Koszul ホモロジーの長さは、係数代数の商を
基底環の標準写像で制限した長さと一致する。商の R 作用を環準同型から明示的に構成する。 -/
theorem length_comap_koszulModuleHomology_zero_quotient
    {R S C : Type u} [CommRing R] [CommRing S] [CommRing C]
    [Algebra R S] [Algebra S C] [Algebra R C] [IsScalarTower R S C]
    {J : Ideal R} (lam : NormalizedLength R J) (K : Ideal S)
    (hK : J.map (algebraMap R S) ≤ K) {r : ℕ} (z : Fin r → S) :
    (lam.comap (algebraMap R S) K hK).len
      (((koszulModuleFunctor z).obj (ModuleCat.of S C)).homology 0) =
    (let _ := Module.compHom (C ⧸ Ideal.span (Set.range (algebraMap S C ∘ z)))
      (algebraMap R C)
     lam.len (C ⧸ Ideal.span (Set.range (algebraMap S C ∘ z)))) := by
  rw [length_comap_koszulModuleHomology lam K hK z 0]
  let H := (koszulComplex (algebraMap S C ∘ z)).homology 0
  let Q := C ⧸ Ideal.span (Set.range (algebraMap S C ∘ z))
  let : Module R H := Module.compHom H (algebraMap R C)
  let : Module R Q := Module.compHom Q (algebraMap R C)
  exact lam.len_congr H Q
    (((ModuleCat.restrictScalars (algebraMap R C)).mapIso
      (LinearEquiv.toModuleIso
        (X₁ := H) (X₂ := ModuleCat.of C Q)
        (koszulComplex_homology_zero_equiv (algebraMap S C ∘ z)).some)).toLinearEquiv)

end SerrePositivity.LengthAlgebra

end KoszulZeroMonotonicityPart
