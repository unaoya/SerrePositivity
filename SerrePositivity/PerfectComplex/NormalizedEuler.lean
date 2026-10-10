module

public import SerrePositivity.HomologicalAlgebra.ConeLES
public import SerrePositivity.HomologicalAlgebra.Tor
public import SerrePositivity.PerfectComplex.Support
public import SerrePositivity.PerfectComplex.K0
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Nilpotent

/-!
# 正規化長さによる Euler 評価

## 概要

正規化長さ `lam : NormalizedLength C J`（`NormalizedLength.lean`）で複体のホモロジーを測った
Euler 評価 `lambdaEuler lam P = Σ (-1)^i λ(H^i(P))` と、`Tor` を測った
`lambdaChi lam φ N = Σ (-1)^i λ(Tor_i^R(C, N))` を定義し、`lambdaEuler` がホモトピー同値で不変
（`lambdaEuler_eq_of_homotopyEquiv`）かつ写像錐について加法的（`lambdaEuler_cone`）であることを
示す。後半では、台つき完全 `T` 複体を `C` に係数拡大した複体の評価 `chiLam`（`Basic.lean`）を `K₀`
上の準同型にする（`chiLamHom_of_finite`）。論文 Lemma 3.5a の「`λ` による Euler 評価は `K_0^{m}(T)`
上の加法的関数」に当たる。

## 方針

加法性は写像錐の長完全列（`HomologicalAlgebra/ConeLES.lean`）による。長完全列
`… → H^i(P) → H^i(Q) → H^i(Cone) → H^{i+1}(P) → …` を三つの短完全列に切り、各項の長さを隣り合う
射の像の長さ `a_i`、`b_i`、`d_i` の和に分解する（`lambdaLengthReal_eq_add_range`）と、交代和を
とったときに相殺して `χ(Cone) = χ(Q) - χ(P)` になる。この分解には、各ホモロジーが `J` の冪で消える
こと（正規化長さの加法性の対象であること）と、長さの有限性が要る。係数環 `C` の Noether 性は
要らない。

通常の長さは `NormalizedLength.ordinary` という特殊な正規化長さなので、通常の Euler 評価 `chiOrd`
の加法性もここから導く（`chiOrd_eq_lambdaEuler_ordinary`、`OrdinaryEuler.lean`）。

## 規約

`lambdaEuler` は実数値。`λ` の値 `ℝ≥0∞` は `toReal` で実数に移し、無限大は `0` になる。`finsum` は
非零項が無限個なら `0` を返す。したがって `lambdaEuler` を通常の有限和として扱うには、有界性と
有限性を別に仮定する。

## 使われ方と残る仮定

`chiLamHom_of_finite` は「係数拡大後のホモロジーの `λ` がすべて有限」という仮定 `hfinite` をとる。
この有限性は `lambdaHomology_koszulComplexOn_ne_top` と
`lambdaHomology_ne_top_of_koszulComplexOn` を組み合わせて証明する。
前者は単一複体・基底による有限直和・項による有限フィルトレーションを順に扱い、
後者は零ホモトピーから得られる直和因子へ有限性を戻す。
論文の設定への適用は `Paper/Lemma3_5/Normalized.lean` の `lemma_3_5a_lam_finite`。
係数環の Noether 性や平坦性は要求しない。
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing
open scoped ENNReal

namespace SerrePositivity

section general

variable {C : Type u} [CommRing C] {J : Ideal C} (lam : NormalizedLength C J)

/-- 複体 `P` のホモロジーを正規化長さ `λ` で測った Euler 評価 `Σ_i (-1)^i λ(H^i(P))`（実数値）。
`toReal` は無限長を `0` に送り、`finsum` は非零項が無限個なら `0` を返すので、通常の有限和として
使うには有界性と有限性が別に要る。`chiLam`（`Basic.lean`）は係数拡大した複体のこれ。 -/
noncomputable def lambdaEuler (P : CochainComplex (ModuleCat.{u} C) ℤ) : ℝ :=
  ∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * (lam.len (P.homology i)).toReal

/-- `Tor` を正規化長さ `λ` で測った Euler 標数 `Σ_i (-1)^i λ(Tor_i^R(C, N))`（実数値）。`C` の `R` 代数
構造は `φ : R →+* C` で与え、`Tor_i^R(C, N)` は `TorAlg φ i N`（`HomologicalAlgebra/Tor.lean`）。
無限の長さは `0` になる。論文 (5.2) の `c_σ` は `φ = ι_σ`（ひねった構造射）、`N = E'` の場合。
`N` の分解 `P` をとれば `lambdaEuler lam (P ⊗ C)` に等しい
（`IntersectionMultiplicity/ResolutionEvaluation.lean`）。 -/
noncomputable def lambdaChi {R : Type u} [CommRing R] (φ : R →+* C)
    (N : Type u) [AddCommGroup N] [Module R N] : ℝ :=
  ∑ᶠ i : ℕ, (-1 : ℝ) ^ i * (lam.len (TorAlg φ i N)).toReal

/-! ## 写像錐による有限性の評価 -/

/-- 写像錐のホモロジーの正規化長さは、両端のホモロジーの長さの和で上から評価される。
三つの加群が `J` 冪ねじれであることだけを仮定し、長さの有限性は要求しない。
有限フィルトレーションの各段で繰り返し使う長完全列の不等式。 -/
lemma lambdaHomology_cone_le {P Q : CochainComplex (ModuleCat.{u} C) ℤ}
    (f : P ⟶ Q) (i : ℤ)
    (tQ : IsPowTorsion J (Q.homology i))
    (tCone : IsPowTorsion J ((Cone.cone f).homology i))
    (tP : IsPowTorsion J (P.homology (i + 1))) :
    lam.len ((Cone.cone f).homology i) ≤
      lam.len (Q.homology i) + lam.len (P.homology (i + 1)) := by
  exact lam.len_le_add_of_exact
    (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr f) i).hom
    (Cone.δ f i (i + 1) rfl).hom
    (LinearMap.exact_iff.mpr (Cone.exact₃ f i (i + 1) rfl).moduleCat_range_eq_ker.symm) tQ tCone tP

/-- 写像錐の両端のホモロジーの正規化長さが有限なら、錐のホモロジーの長さも有限。
`lambdaHomology_cone_le` と有限な二つの長さの和の有限性による。 -/
lemma lambdaHomology_cone_ne_top {P Q : CochainComplex (ModuleCat.{u} C) ℤ}
    (f : P ⟶ Q) (i : ℤ)
    (tQ : IsPowTorsion J (Q.homology i))
    (tCone : IsPowTorsion J ((Cone.cone f).homology i))
    (tP : IsPowTorsion J (P.homology (i + 1)))
    (hQ : lam.len (Q.homology i) ≠ ⊤)
    (hP : lam.len (P.homology (i + 1)) ≠ ⊤) :
    lam.len ((Cone.cone f).homology i) ≠ ⊤ :=
  ne_top_of_le_ne_top (WithTop.add_ne_top.mpr ⟨hQ, hP⟩)
    (lambdaHomology_cone_le lam f i tQ tCone tP)

/-- 零ホモトピックな射 `f : P → Q` では `H^i(Q) → H^i(Cone f)` が単射となるので、
錐のホモロジーの長さが有限なら `H^i(Q)` の長さも有限。
Koszul の錐から元の複体へ有限性を戻すための一般論で、錐の直和分解の構成は不要。 -/
lemma lambdaHomology_ne_top_of_nullHomotopic_cone
    {P Q : CochainComplex (ModuleCat.{u} C) ℤ} (f : P ⟶ Q)
    (hf : Homotopy f 0) (i : ℤ)
    (tCone : IsPowTorsion J ((Cone.cone f).homology i))
    (hCone : lam.len ((Cone.cone f).homology i) ≠ ⊤) :
    lam.len (Q.homology i) ≠ ⊤ := by
  have hzero : HomologicalComplex.homologyMap f i = 0 := by
    simpa only [HomologicalComplex.homologyMap_zero] using hf.homologyMap_eq i
  have : Mono (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr f) i) :=
    (Cone.exact₂ f i).mono_g hzero
  exact ne_top_of_le_ne_top hCone (lam.len_le_of_injective
    (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr f) i).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance) tCone)

/-- 複体 `P` が `Q` の直和因子なら、ホモロジーも直和因子となる。
`Q` のホモロジーが `J` 冪ねじれで正規化長さが有限なら、`P` のホモロジーの長さも有限。 -/
lemma lambdaHomology_ne_top_of_retract {P Q : CochainComplex (ModuleCat.{u} C) ℤ}
    (h : Retract P Q) (i : ℤ) (tQ : IsPowTorsion J (Q.homology i))
    (hQ : lam.len (Q.homology i) ≠ ⊤) : lam.len (P.homology i) ≠ ⊤ := by
  let hh := h.map (HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (ComplexShape.up ℤ) i)
  exact ne_top_of_le_ne_top hQ (lam.len_le_of_injective hh.i.hom
    ((ModuleCat.mono_iff_injective hh.i).mp inferInstance) tQ)

/-- 複体の短完全列で、両端の同じ次数のホモロジーの正規化長さが有限なら、中央も有限。
ホモロジーの長完全列の三項部分と、冪ねじれ加群上の長さの加法性を使う。 -/
lemma lambdaHomology_shortExact_ne_top
    (S : ShortComplex (CochainComplex (ModuleCat.{u} C) ℤ)) (hS : S.ShortExact) (i : ℤ)
    (t₁ : IsPowTorsion J (S.X₁.homology i))
    (t₂ : IsPowTorsion J (S.X₂.homology i))
    (t₃ : IsPowTorsion J (S.X₃.homology i))
    (h₁ : lam.len (S.X₁.homology i) ≠ ⊤) (h₃ : lam.len (S.X₃.homology i) ≠ ⊤) :
    lam.len (S.X₂.homology i) ≠ ⊤ :=
  lam.len_ne_top_of_exact (HomologicalComplex.homologyMap S.f i).hom
    (HomologicalComplex.homologyMap S.g i).hom
    (LinearMap.exact_iff.mpr (hS.homology_exact₂ i).moduleCat_range_eq_ker.symm)
    t₁ t₂ t₃ h₁ h₃

/-- 完全列 `M →f N →g L` の中央の長さは、二つの射の像の長さの和：`λ(N) = λ(im f) + λ(im g)`
（実数値）。`λ(N) = λ(ker g) + λ(im g)`（`len_eq_add_ker_range`）と `ker g = im f` による。`N` が `J` の
冪で消えること（加法性の対象であること）と `λ(N) < ∞`（`toReal` で和が保たれること）が要る。
長完全列の各項をこの形に分解するのが `lambdaEuler_cone` の要点。 -/
lemma lambdaLengthReal_eq_add_range {M N L : Type u} [AddCommGroup M] [Module C M]
    [AddCommGroup N] [Module C N] [AddCommGroup L] [Module C L]
    (f : M →ₗ[C] N) (g : N →ₗ[C] L) (hfg : Function.Exact f g)
    (tN : IsPowTorsion J N) (hN : lam.len N ≠ ⊤) :
    (lam.len N).toReal = (lam.len (LinearMap.range f)).toReal +
      (lam.len (LinearMap.range g)).toReal := by
  have hk : lam.len (LinearMap.ker g) ≠ ⊤ :=
    ne_top_of_le_ne_top hN (lam.len_submodule_le tN _)
  have hr : lam.len (LinearMap.range g) ≠ ⊤ :=
    ne_top_of_le_ne_top hN (lam.len_range_le g tN)
  rw [lam.len_eq_add_ker_range g tN, ENNReal.toReal_add hk hr,
    ← LinearMap.exact_iff.mp hfg]

/-- 有界な複体では、`i ↦ λ(H^i(P))`（実数値）は有限個の `i` でしか `0` でない（範囲の外ではホモロジーが
零だから）。`finsum` を通常の有限和として扱うための条件。 -/
lemma lambdaHomology_hasFiniteSupport (P : CochainComplex (ModuleCat.{u} C) ℤ)
    (hP : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (P.X i)) :
    Function.HasFiniteSupport (fun i ↦ (lam.len (P.homology i)).toReal) := by
  obtain ⟨a, b, hab⟩ := hP
  apply (Set.finite_Icc a b).subset
  intro i hi
  by_contra hn
  have hzero : IsZero (P.homology i) :=
    (P.sc i).isZero_homology_of_isZero_X₂ (hab i (by simp only [Set.mem_Icc] at hn; omega))
  have := ModuleCat.subsingleton_of_isZero hzero
  exact hi (by simp [lam.len_eq_zero_of_subsingleton])

/-- ホモトピー同値な複体の `lambdaEuler` は等しい。各次数のホモロジーが線形同型で、`λ` は同型で
不変だから。有限性・有界性の仮定は要らない（両辺が規約どおりに同じ値をとる）。 -/
lemma lambdaEuler_eq_of_homotopyEquiv {P Q : CochainComplex (ModuleCat.{u} C) ℤ}
    (h : HomotopyEquiv P Q) : lambdaEuler lam P = lambdaEuler lam Q := by
  unfold lambdaEuler
  congr 1
  funext i
  rw [lam.len_congr _ _ (h.toHomologyIso i).toLinearEquiv]

/-- 交代和の添字を一つずらすと符号が反転する：`Σ (-1)^i f(i - 1) = -Σ (-1)^i f(i)`。`finsum` の
規約（非零項が無限個なら `0`）を含めて成り立つ。 -/
private lemma alternating_finsum_shift (f : ℤ → ℝ) :
    (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * f (i - 1)) =
      -(∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * f i) := by
  calc
    _ = ∑ᶠ i : ℤ, (((i + 1).negOnePow : ℤ) : ℝ) * f i := by
      have h := finsum_comp_equiv (Equiv.addRight (1 : ℤ))
        (f := fun i : ℤ ↦ ((i.negOnePow : ℤ) : ℝ) * f (i - 1))
      simpa using h.symm
    _ = ∑ᶠ i : ℤ, -(((i.negOnePow : ℤ) : ℝ) * f i) := by
      congr 1
      funext i
      simp [Int.negOnePow_add]
    _ = _ := finsum_neg_distrib _

set_option maxHeartbeats 800000 in
-- ホモロジーの対象に依存する型を含む三つの完全列の移送に、追加の処理時間を許す。
/-- **写像錐についての加法性**：`f : P ⟶ Q` について `λ-χ(Cone f) = λ-χ(Q) - λ-χ(P)`。仮定は、`Q` と
`Cone f` が有界で、`P`、`Q`、`Cone f` の各ホモロジーが `J` の冪で消え、`λ` が有限であること。

証明は長完全列（`Cone.exact₁₂₃`）による。`a_i = λ(im H^i(f))`、`b_i = λ(im H^i(inr))`、
`d_i = λ(im δ_i)` とおくと、`lambdaLengthReal_eq_add_range` により `λ(H^i(Q)) = a_i + b_i`、
`λ(H^i(Cone f)) = b_i + d_i`、`λ(H^{i+1}(P)) = d_i + a_{i+1}`。交代和をとると
`χ(Q) = A + B`、`χ(Cone) = B + D`、`χ(P) = -D + A`（添字のずれで符号が反転、
`alternating_finsum_shift`）で、`χ(Cone) = χ(Q) - χ(P)`。`finsum` を分配するために各列が有限な台を
もつことを確かめる。係数環の Noether 性は要らない。 -/
theorem lambdaEuler_cone {P Q : CochainComplex (ModuleCat.{u} C) ℤ} (f : P ⟶ Q)
    (hQ : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (Q.X i))
    (hC : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero ((Cone.cone f).X i))
    (tP : ∀ i, IsPowTorsion J (P.homology i))
    (tQ : ∀ i, IsPowTorsion J (Q.homology i))
    (tC : ∀ i, IsPowTorsion J ((Cone.cone f).homology i))
    (lP : ∀ i, lam.len (P.homology i) ≠ ⊤)
    (lQ : ∀ i, lam.len (Q.homology i) ≠ ⊤)
    (lC : ∀ i, lam.len ((Cone.cone f).homology i) ≠ ⊤) :
    lambdaEuler lam (Cone.cone f) = lambdaEuler lam Q - lambdaEuler lam P := by
  let α := fun i ↦ (HomologicalComplex.homologyMap f i).hom
  let β := fun i ↦ (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr f) i).hom
  let δ := fun i ↦ (Cone.δ f i (i + 1) rfl).hom
  let a := fun i ↦ (lam.len (LinearMap.range (α i))).toReal
  let b := fun i ↦ (lam.len (LinearMap.range (β i))).toReal
  let d := fun i ↦ (lam.len (LinearMap.range (δ i))).toReal
  have ha : Function.HasFiniteSupport a := by
    apply (lambdaHomology_hasFiniteSupport lam Q hQ).subset
    intro i hi hz
    have hz' : lam.len (Q.homology i) = 0 := by
      have hn := lQ i
      simpa [ENNReal.toReal_eq_zero_iff, hn] using hz
    have : lam.len (LinearMap.range (α i)) = 0 :=
      le_antisymm (hz' ▸ lam.len_submodule_le (tQ i) _) bot_le
    exact hi (by simp [a, this])
  have hb : Function.HasFiniteSupport b := by
    apply (lambdaHomology_hasFiniteSupport lam (Cone.cone f) hC).subset
    intro i hi hz
    have hz' : lam.len ((Cone.cone f).homology i) = 0 := by
      have hn := lC i
      simpa [ENNReal.toReal_eq_zero_iff, hn] using hz
    have : lam.len (LinearMap.range (β i)) = 0 :=
      le_antisymm (hz' ▸ lam.len_submodule_le (tC i) _) bot_le
    exact hi (by simp [b, this])
  have hd : Function.HasFiniteSupport d := by
    apply (lambdaHomology_hasFiniteSupport lam (Cone.cone f) hC).subset
    intro i hi hz
    have hz' : lam.len ((Cone.cone f).homology i) = 0 := by
      have hn := lC i
      simpa [ENNReal.toReal_eq_zero_iff, hn] using hz
    have : lam.len (LinearMap.range (δ i)) = 0 :=
      le_antisymm (hz' ▸ lam.len_range_le (δ i) (tC i)) bot_le
    exact hi (by simp [d, this])
  have hQlen : ∀ i, ((lam.len (Q.homology i)).toReal : ℝ) = a i + b i := fun i ↦
    lambdaLengthReal_eq_add_range lam (α i) (β i)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
        (Cone.exact₂ f i)) (tQ i) (lQ i)
  have hClen : ∀ i, ((lam.len ((Cone.cone f).homology i)).toReal : ℝ) = b i + d i := fun i ↦
    lambdaLengthReal_eq_add_range lam (β i) (δ i)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
        (Cone.exact₃ f i (i + 1) rfl)) (tC i) (lC i)
  have hPlen : ∀ i, ((lam.len (P.homology i)).toReal : ℝ) = d (i - 1) + a i := by
    intro i
    obtain ⟨j, rfl⟩ : ∃ j : ℤ, i = j + 1 := ⟨i - 1, by omega⟩
    rw [add_sub_cancel_right]
    exact lambdaLengthReal_eq_add_range lam (δ j) (α (j + 1))
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
        (Cone.exact₁ f j (j + 1) rfl)) (tP (j + 1)) (lP (j + 1))
  have haw : Function.HasFiniteSupport (fun i : ℤ ↦ ((i.negOnePow : ℤ) : ℝ) * a i) :=
    ha.mul_right _
  have hbw : Function.HasFiniteSupport (fun i : ℤ ↦ ((i.negOnePow : ℤ) : ℝ) * b i) :=
    hb.mul_right _
  have hdw : Function.HasFiniteSupport (fun i : ℤ ↦ ((i.negOnePow : ℤ) : ℝ) * d i) :=
    hd.mul_right _
  have hds : Function.HasFiniteSupport (fun i : ℤ ↦ ((i.negOnePow : ℤ) : ℝ) * d (i - 1)) := by
    have hdp : Function.HasFiniteSupport (fun i : ℤ ↦ d (i - 1)) :=
      hd.preimage (Equiv.subRight (1 : ℤ)).injective.injOn
    exact hdp.mul_right _
  have eQ : lambdaEuler lam Q = (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * a i) +
      (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * b i) := by
    simp_rw [lambdaEuler, hQlen, mul_add]
    exact finsum_add_distrib haw hbw
  have eC : lambdaEuler lam (Cone.cone f) = (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * b i) +
      (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * d i) := by
    simp_rw [lambdaEuler, hClen, mul_add]
    exact finsum_add_distrib hbw hdw
  have eP : lambdaEuler lam P = -(∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * d i) +
      (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * a i) := by
    simp_rw [lambdaEuler, hPlen, mul_add]
    rw [finsum_add_distrib hds haw, alternating_finsum_shift]
  rw [eC, eQ, eP]
  ring

/-- `w` に台をもつ複体のホモロジーは、`J ⊆ √(w)` なる有限生成イデアル `J` の冪で消える。台の条件から
`(w) ⊆ √(Ann H^i(P))`（`IsSupported.le_radical_annihilator`）なので `J ⊆ √(Ann H^i(P))`、あとは
`IsPowTorsion.of_le_radical_annihilator`。正規化長さの加法性の対象であることの根拠。 -/
lemma supported_homology_isPowTorsion (hfg : J.FG) {n : ℕ}
    {w : Fin n → C} (hJ : J ≤ (Ideal.span (Set.range w)).radical)
    {P : CochainComplex (ModuleCat.{u} C) ℤ} (hP : IsSupported w P) (i : ℤ) :
    IsPowTorsion J (P.homology i) :=
  IsPowTorsion.of_le_radical_annihilator hfg (hJ.trans (by
    have h := Ideal.radical_mono (hP.le_radical_annihilator i)
    simpa only [Ideal.radical_idem] using h))

/-- 各元の作用が零ホモトピックなら、係数つき Koszul 複体のホモロジーの有限性は
元の複体へ戻る。冪ねじれ性は `J` の有限生成性と `J ⊆ √(x)` から導く。
有界性や項の自由性はこの引き戻し自体には必要ない。 -/
lemma lambdaHomology_ne_top_of_koszulComplexOn (hfg : J.FG) {n : ℕ}
    (x : Fin n → C) (hJ : J ≤ (Ideal.span (Set.range x)).radical)
    (P : CochainComplex (ModuleCat.{u} C) ℤ)
    (h : ∀ j, Nonempty (Homotopy (smulId (x j) P) 0)) (i : ℤ)
    (hfinite : lam.len ((koszulComplexOn x P).homology i) ≠ ⊤) :
    lam.len (P.homology i) ≠ ⊤ :=
  lambdaHomology_ne_top_of_retract lam (retractKoszulComplexOn x P h) i
    (supported_homology_isPowTorsion hfg hJ (isSupported_koszulComplexOn x P) i) hfinite

/-- 係数つき Koszul ホモロジーの有限性を、有限自由加群の単一複体の場合へ帰着する。
係数複体の項による有限フィルトレーションを `boundedFiniteFree_induction` で扱い、
Koszul 関手の完全性とホモロジーの長完全列で各段の有限性を伝える。 -/
lemma lambdaHomology_koszulComplexOn_ne_top_of_single (hfg : J.FG) {n : ℕ}
    (x : Fin n → C) (hJ : J ≤ (Ideal.span (Set.range x)).radical)
    (hsingle : ∀ (a : ℤ) (M : ModuleCat.{u} C), Module.Free C M → Module.Finite C M →
      ∀ i : ℤ, lam.len ((koszulComplexOn x
        ((HomologicalComplex.single _ _ a).obj M)).homology i) ≠ ⊤)
    (P : CochainComplex (ModuleCat.{u} C) ℤ)
    (hfree : ∀ i, Module.Free C (P.X i)) (hfinite : ∀ i, Module.Finite C (P.X i))
    (hbounded : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (P.X i)) (i : ℤ) :
    lam.len ((koszulComplexOn x P).homology i) ≠ ⊤ := by
  let F := koszulFunctor x
  have ht (Q : CochainComplex (ModuleCat.{u} C) ℤ) (j : ℤ) :
      IsPowTorsion J ((F.obj Q).homology j) := by
    exact
      supported_homology_isPowTorsion hfg hJ (isSupported_koszulComplexOn x Q) j
  suffices h : ∀ j : ℤ, lam.len ((F.obj P).homology j) ≠ ⊤ by
    exact h i
  apply boundedFiniteFree_induction (fun Q ↦ ∀ j : ℤ, lam.len ((F.obj Q).homology j) ≠ ⊤)
    ?_ ?_ ?_ P hfree hfinite hbounded
  · intro Q hQ j
    have hz :=
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (ComplexShape.up ℤ) j).map_isZero
      (F.map_isZero hQ)
    have : Subsingleton ((F.obj Q).homology j) := ModuleCat.isZero_iff_subsingleton.mp hz
    rw [lam.len_eq_zero_of_subsingleton]
    exact ENNReal.zero_ne_top
  · intro a M hMfree hMfinite j
    exact hsingle a M hMfree hMfinite j
  · intro S hS h₁ h₃ j
    exact lambdaHomology_shortExact_ne_top lam (S.map F) (koszulFunctor_shortExact x S hS) j
      (ht S.X₁ j) (ht S.X₂ j) (ht S.X₃ j) (h₁ j) (h₃ j)

/-- 環を任意の一つの次数に置いた係数複体の場合、Koszul ホモロジーの有限性は
通常の Koszul 複体の有限性からシフト同型によって従う。 -/
lemma lambdaHomology_koszul_single_ring {n : ℕ} (x : Fin n → C)
    (hfin : ∀ i : ℤ, lam.len ((koszulComplex x).homology i) ≠ ⊤) (a i : ℤ) :
    lam.len ((koszulComplexOn x
      ((HomologicalComplex.single _ _ a).obj (ModuleCat.of C C))).homology i) ≠ ⊤ := by
  let P := (HomologicalComplex.single (ModuleCat.{u} C) (ComplexShape.up ℤ) 0).obj
    (ModuleCat.of C C)
  let e := ((CochainComplex.singleFunctors (ModuleCat.{u} C)).shiftIso (-a) a 0 (by omega)).app
    (ModuleCat.of C C)
  let eK : koszulComplexOn x ((HomologicalComplex.single _ _ a).obj (ModuleCat.of C C)) ≅
      (koszulComplex x)⟦-a⟧ :=
    (koszulFunctor x).mapIso e.symm ≪≫ (koszulComplexOnShiftIso x P (-a)).symm ≪≫
      (shiftFunctor _ (-a)).mapIso (eqToIso (koszulComplexOn_single x))
  let eh :=
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (ComplexShape.up ℤ) i).mapIso eK ≪≫
    (CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} C) (-a) i (i - a) (by omega)).app
      (koszulComplex x)
  exact ne_of_eq_of_ne (lam.len_congr _ _ eh.toLinearEquiv) (hfin _)

/-- 有限自由加群を一つの次数に置いた係数複体では、Koszul ホモロジーの正規化長さは有限。
基底の個数について帰納し、環の場合と直積の分裂短完全列に帰着する。 -/
lemma lambdaHomology_koszul_single_finiteFree (hfg : J.FG) {n : ℕ}
    (x : Fin n → C) (hJ : J ≤ (Ideal.span (Set.range x)).radical)
    (hfin : ∀ i : ℤ, lam.len ((koszulComplex x).homology i) ≠ ⊤)
    (a : ℤ) (M : ModuleCat.{u} C) [Module.Free C M] [Module.Finite C M] (i : ℤ) :
    lam.len ((koszulComplexOn x ((HomologicalComplex.single _ _ a).obj M)).homology i) ≠ ⊤ := by
  let F := HomologicalComplex.single (ModuleCat.{u} C) (ComplexShape.up ℤ) a ⋙ koszulFunctor x
  have ht (N : ModuleCat.{u} C) : IsPowTorsion J ((F.obj N).homology i) :=
    supported_homology_isPowTorsion hfg hJ (isSupported_koszulComplexOn x _) i
  change lam.len ((F.obj M).homology i) ≠ ⊤
  apply finiteFree_module_induction (fun N ↦ lam.len ((F.obj N).homology i) ≠ ⊤) ?_ ?_ ?_ ?_ M
  · intro N hN
    have hz :=
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (ComplexShape.up ℤ) i).map_isZero
      (F.map_isZero hN)
    have : Subsingleton ((F.obj N).homology i) := ModuleCat.isZero_iff_subsingleton.mp hz
    rw [lam.len_eq_zero_of_subsingleton]
    exact ENNReal.zero_ne_top
  · exact lambdaHomology_koszul_single_ring lam x hfin a i
  · intro N N' e hN
    let eh := (HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (ComplexShape.up ℤ) i).mapIso
      (F.mapIso e)
    exact ne_of_eq_of_ne (lam.len_congr _ _ eh.toLinearEquiv).symm hN
  · intro N N' hN hN'
    let S : ShortComplex (ModuleCat.{u} C) :=
      ModuleCat.shortComplexOfCompEqZero (LinearMap.inl C N N') (LinearMap.snd C N N') (by ext; rfl)
    have hS : S.ShortExact := by
      refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
      · rw [ShortComplex.moduleCat_exact_iff]
        intro y hy
        exact ⟨y.1, Prod.ext rfl hy.symm⟩
      · exact (ModuleCat.mono_iff_injective _).mpr (fun y z h ↦ congrArg Prod.fst h)
      · exact (ModuleCat.epi_iff_surjective _).mpr (fun y ↦ ⟨(0, y), rfl⟩)
    have := hS.mono_f
    have := hS.epi_g
    have hs := hS.map (HomologicalComplex.single (ModuleCat.{u} C) (ComplexShape.up ℤ) a)
    exact lambdaHomology_shortExact_ne_top lam
      ((S.map (HomologicalComplex.single _ _ a)).map (koszulFunctor x))
      (koszulFunctor_shortExact x _ hs) i (ht N) (ht _) (ht N') hN hN'

/-- 通常の Koszul ホモロジーの正規化長さが全次数で有限なら、有界有限自由複体 `P` を
係数とする Koszul ホモロジーの長さも有限。単一次数の有限自由加群の場合を基底分解で示し、
項による有限フィルトレーションを使って一般の複体へ広げる。 -/
lemma lambdaHomology_koszulComplexOn_ne_top (hfg : J.FG) {n : ℕ}
    (x : Fin n → C) (hJ : J ≤ (Ideal.span (Set.range x)).radical)
    (hfin : ∀ j : ℤ, lam.len ((koszulComplex x).homology j) ≠ ⊤)
    (P : CochainComplex (ModuleCat.{u} C) ℤ)
    (hfree : ∀ j, Module.Free C (P.X j)) (hfinite : ∀ j, Module.Finite C (P.X j))
    (hbounded : ∃ a b : ℤ, ∀ j, (j < a ∨ b < j) → IsZero (P.X j)) (i : ℤ) :
    lam.len ((koszulComplexOn x P).homology i) ≠ ⊤ := by
  apply lambdaHomology_koszulComplexOn_ne_top_of_single lam hfg x hJ ?_ P hfree hfinite hbounded i
  intro a M hMfree hMfinite j
  have := hMfree
  have := hMfinite
  exact lambdaHomology_koszul_single_finiteFree lam hfg x hJ hfin a M j

/-! ## 通常の長さを正規化長さの特殊例として扱う -/

/-- `ℕ∞` の値を `ℝ≥0∞` 経由で実数に移しても、`toNat` 経由で移しても同じ（どちらも `⊤` を `0` に
送る）。`chiOrd`（`toNat` 経由）と `lambdaEuler (ordinary T)`（`toReal` 経由）を比べるのに使う。 -/
lemma toReal_toENNReal (n : ℕ∞) : (n : ℝ≥0∞).toReal = (n.toNat : ℝ) := by
  induction n using ENat.recTopCoe with
  | top => simp
  | coe k => simp

/-- 通常の Euler 評価 `chiOrd` は、正規化長さとして通常の長さ `NormalizedLength.ordinary T` をとった
`lambdaEuler` に等しい。これで `lambdaEuler` の定理が `chiOrd` に特殊化できる（`OrdinaryEuler.lean`）。 -/
lemma chiOrd_eq_lambdaEuler_ordinary {T : Type u} [CommRing T]
    (P : CochainComplex (ModuleCat.{u} T) ℤ) :
    chiOrd P = lambdaEuler (NormalizedLength.ordinary T) P := by
  unfold chiOrd lambdaEuler
  simp only [NormalizedLength.ordinary_len, toReal_toENNReal]

end general

/-! ## 台つき完全複体の正規化 Euler 評価

論文 Lemma 3.5a の設定：環の塔 `A → T → C`（`A` は Noether 局所環）、`√(z) = m_A` なる `A` の元の列
`z`、`m_A C` の冪ねじれ加群の上で加法的な正規化長さ `lam`。`z` に台をもつ完全 `T` 複体 `P` を `C` に
係数拡大した `P ⊗_T C` のホモロジーは `m_A C` の冪で消える（`chiLam_homology_isPowTorsion`）ので、
`lam` の加法性の対象になる。その長さの有限性を仮定して、`chiLam lam (algebraMap T C) P` を
`K₀^{(z)}(T)` 上の準同型にする（`chiLamHom_of_finite`）。
-/

section supported

variable {A T C : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing T]
  [Algebra A T] [CommRing C] [Algebra T C] [Algebra A C] [IsScalarTower A T C]
  {e : ℕ} {z : Fin e → A} {lam : NormalizedLength C ((maximalIdeal A).map (algebraMap A C))}

/-- `√(z) = m_A` のとき、`z` に台をもつ完全 `T` 複体 `P` の係数拡大 `P ⊗_T C` のホモロジーは `m_A C` の
冪で消える。`P ⊗_T C` は `z` の `C` での像に台をもち（`isSupported_baseChange`）、
`m_A C = (√(z)) C ⊆ √((z) C)` なので `supported_homology_isPowTorsion` が使える。`m_A` が有限生成で
あることに `A` の Noether 性を使う。 -/
lemma chiLam_homology_isPowTorsion
    (hz : (Ideal.span (Set.range z)).radical = maximalIdeal A)
    {P : CochainComplex (ModuleCat.{u} T) ℤ}
    (hP : IsPerfectSupported (algebraMap A T ∘ z) P) (i : ℤ) :
    IsPowTorsion ((maximalIdeal A).map (algebraMap A C))
      ((baseChange (algebraMap T C) P).homology i) := by
  have hfg := (maximalIdeal A).fg_of_isNoetherianRing.map (algebraMap A C)
  have hJ : (maximalIdeal A).map (algebraMap A C) ≤
      (Ideal.span (Set.range (algebraMap A C ∘ z))).radical := by
    have h := Ideal.map_radical_le (algebraMap A C) (I := Ideal.span (Set.range z))
    rw [hz, Ideal.map_span, ← Set.range_comp] at h
    exact h
  have hs : IsSupported (algebraMap A C ∘ z) (baseChange (algebraMap T C) P) := by
    have h := isSupported_baseChange (algebraMap T C) hP.supported
    have heq : algebraMap T C ∘ (algebraMap A T ∘ z) = algebraMap A C ∘ z := by
      funext j
      exact (IsScalarTower.algebraMap_apply A T C (z j)).symm
    rwa [heq] at h
  exact supported_homology_isPowTorsion hfg hJ hs i

omit [IsNoetherianRing A] [Algebra A T] [Algebra T C] [IsScalarTower A T C] in
/-- `chiLam` はもとの複体のホモトピー同値で不変（係数拡大はホモトピー同値を保つ）。 -/
lemma chiLam_eq_of_homotopyEquiv (φ : T →+* C)
    {P Q : CochainComplex (ModuleCat.{u} T) ℤ} (h : HomotopyEquiv P Q) :
    chiLam lam φ P = chiLam lam φ Q :=
  lambdaEuler_eq_of_homotopyEquiv lam ((ModuleCat.extendScalars φ).mapHomotopyEquiv h)

/-- 係数拡大後のホモロジーの `λ` がすべて有限（`hfinite`）なら、`chiLam` は錐の関係式
`chiLam (Cone f) = chiLam Q - chiLam P` をみたす。係数拡大は写像錐と可換
（`(Cone f) ⊗_T C ≅ Cone(f ⊗_T C)`）なので、`lambdaEuler_cone` を `f ⊗_T C` に適用する。冪ねじれの
条件は `chiLam_homology_isPowTorsion`、有界性は `baseChange_bounded`。 -/
lemma chiLam_cone_of_finite
    (hz : (Ideal.span (Set.range z)).radical = maximalIdeal A)
    (hfinite : ∀ (P : PerfSupp T (algebraMap A T ∘ z)) (i : ℤ),
      lam.len ((baseChange (algebraMap T C) P.1).homology i) ≠ ⊤)
    (P Q : PerfSupp T (algebraMap A T ∘ z)) (f : P.1 ⟶ Q.1)
    (hc : IsPerfectSupported (algebraMap A T ∘ z) (CochainComplex.mappingCone f)) :
    chiLam lam (algebraMap T C) (CochainComplex.mappingCone f) =
      chiLam lam (algebraMap T C) Q.1 - chiLam lam (algebraMap T C) P.1 := by
  let F := ModuleCat.extendScalars.{u, u, u} (algebraMap T C)
  let fC := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map f
  let k : baseChange (algebraMap T C) (CochainComplex.mappingCone f) ≅ Cone.cone fC :=
    HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjIso f F
  have hbound : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero ((Cone.cone fC).X i) := by
    obtain ⟨a, b, hab⟩ := baseChange_bounded (algebraMap T C) _ hc.bounded
    exact ⟨a, b, fun i hi ↦ (HomologicalComplex.Hom.isoApp k i).isZero_iff.mp (hab i hi)⟩
  have tC : ∀ i, IsPowTorsion ((maximalIdeal A).map (algebraMap A C))
      ((Cone.cone fC).homology i) := fun i ↦
    IsPowTorsion.of_equiv
      (((HomologicalComplex.homologyFunctor _ _ i).mapIso k).toLinearEquiv)
      (chiLam_homology_isPowTorsion hz hc i)
  have lC : ∀ i, lam.len ((Cone.cone fC).homology i) ≠ ⊤ := by
    intro i
    have hi := lam.len_congr _ _
      (((HomologicalComplex.homologyFunctor _ _ i).mapIso k).toLinearEquiv)
    exact ne_of_eq_of_ne hi.symm (hfinite ⟨_, hc⟩ i)
  change lambdaEuler lam (baseChange (algebraMap T C) (CochainComplex.mappingCone f)) =
    lambdaEuler lam (baseChange (algebraMap T C) Q.1) -
      lambdaEuler lam (baseChange (algebraMap T C) P.1)
  rw [lambdaEuler_eq_of_homotopyEquiv lam (HomotopyEquiv.ofIso k)]
  exact lambdaEuler_cone lam fC
    (baseChange_bounded (algebraMap T C) _ Q.2.bounded) hbound
    (chiLam_homology_isPowTorsion hz P.2) (chiLam_homology_isPowTorsion hz Q.2) tC
    (hfinite P) (hfinite Q) lC

/-- 有限性の仮定 `hfinite` のもとで、`chiLam` を `K₀^{(z)}(T)` から `ℝ` への準同型に降ろしたもの。
`K0.lift` にホモトピー不変性と錐の関係式を渡す。Lemma 3.5a・3.5b の正規化長さ側
（`Paper/Lemma3_5/Normalized.lean`）で、`K0.hom_ext_koszul` と組み合わせて使う。 -/
noncomputable def chiLamHom_of_finite
    (hz : (Ideal.span (Set.range z)).radical = maximalIdeal A)
    (hfinite : ∀ (P : PerfSupp T (algebraMap A T ∘ z)) (i : ℤ),
      lam.len ((baseChange (algebraMap T C) P.1).homology i) ≠ ⊤) :
    K0Supported T (algebraMap A T ∘ z) →+ ℝ :=
  K0.lift (fun P ↦ chiLam lam (algebraMap T C) P.1)
    (fun _ _ h ↦ chiLam_eq_of_homotopyEquiv (algebraMap T C) h)
    (chiLam_cone_of_finite hz hfinite)

/-- `chiLamHom_of_finite [P] = chiLam lam (algebraMap T C) P`。 -/
@[simp]
lemma chiLamHom_of_finite_mk
    (hz : (Ideal.span (Set.range z)).radical = maximalIdeal A)
    (hfinite : ∀ (P : PerfSupp T (algebraMap A T ∘ z)) (i : ℤ),
      lam.len ((baseChange (algebraMap T C) P.1).homology i) ≠ ⊤)
    (P : PerfSupp T (algebraMap A T ∘ z)) :
    chiLamHom_of_finite hz hfinite (K0.mk P) = chiLam lam (algebraMap T C) P.1 :=
  K0.lift_mk _ _ _ _

end supported

end SerrePositivity
