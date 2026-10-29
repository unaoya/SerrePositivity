module

public import Mathlib.RingTheory.Derivation.MapCoeffs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import SerrePositivity.LinearAlgebra.IndependentPerturbation

/-! # 導分の一般論

概要：可換環上の加群値導分 `δ : Derivation R S V` についての一般的な事実。
- 降下：全射 `S → T` の核を消す導分は、`T` 加群に値を持つまま `T` の導分へ降りる（`descendModuleDerivation`）。
- 係数作用：多項式の係数に `δ` を作用させて `x` で評価する線形写像（`coefficientEvalLinearMap`）と Leibniz 則。
- 生成：代数の生成元の像が導分の像全体と同じ部分加群を張る。標数 `p` では導分は `p` 乗を消す。
- イデアル：導分はイデアル冪の次数を高々一つ下げる。整域では非零イデアルの元の像が分数体上で全体を張り、
  有限個のベクトルをその像で摂動して独立にできる。
方針：降下は Mathlib の `LinearMap.liftOfSurjective` で線形写像を降ろしてから Leibniz 則を確かめる。
Mathlib の `Derivation.liftOfSurjective` は自分自身に値を持つ導分に限られ、ここでの版はその一般化。
係数作用は Mathlib の `Derivation.mapCoeffs` と `PolynomialModule.eval` の合成で、`Derivation.apply_aeval_eq'`
の右辺の第一項に当たる。
規約：有限性・Noether 性・局所性は仮定しない。
使われ方：一元添加への導分の延長（FieldTheory の `AdjoinSingletonDerivation`）、p 基底の微分、
Cohen–Gabber の微分パラメータの選択。Mathlib への提出候補（mathlib-upstream）。
-/

@[expose] public noncomputable section
namespace SerrePositivity
open Polynomial

section Descent

variable {R S T V : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  [AddCommGroup V] [Module R V] [Module S V] [Module T V] [IsScalarTower S T V]

/-- 全射の核を消す加群値導分を、その同じ加群へ降ろす。 -/
def descendModuleDerivation (hf : Function.Surjective (algebraMap S T))
    (δ : Derivation R S V) (hδ : ∀ x, algebraMap S T x = 0 → δ x = 0) :
    Derivation R T V := by
  let f := (IsScalarTower.toAlgHom R S T).toLinearMap
  have hk : LinearMap.ker f ≤ LinearMap.ker δ.toLinearMap := fun x hx ↦ hδ x hx
  let g := f.liftOfSurjective hf ⟨δ.toLinearMap, hk⟩
  have hg (x : S) : g (algebraMap S T x) = δ x :=
    LinearMap.equivOfSurjective_apply hf hk
  refine { toLinearMap := g, map_one_eq_zero' := ?_, leibniz' := ?_ }
  · rw [← map_one (algebraMap S T), hg, δ.map_one_eq_zero]
  · intro x y
    obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, rfl⟩ := hf y
    rw [← map_mul, hg, hg, hg]
    simpa only [algebraMap_smul] using δ.leibniz a b

@[simp] theorem descendModuleDerivation_apply (hf : Function.Surjective (algebraMap S T))
    (δ : Derivation R S V) (hδ : ∀ x, algebraMap S T x = 0 → δ x = 0) (x : S) :
    descendModuleDerivation hf δ hδ (algebraMap S T x) = δ x :=
  LinearMap.equivOfSurjective_apply hf _

end Descent

section CoefficientEval

variable {R K L V : Type*} [CommRing R] [CommRing K] [CommRing L]
  [Algebra R K] [Algebra R L] [Algebra K L]
  [AddCommGroup V] [Module R V] [Module K V] [Module L V]
  [IsScalarTower R K V] [IsScalarTower R L V] [IsScalarTower K L V]

/-- 係数の導分を取り、変数をxに評価するR線形写像。 -/
def coefficientEvalLinearMap (x : L) (δ : Derivation R K V) : K[X] →ₗ[R] V := by
  let : IsScalarTower R K (PolynomialModule L V) :=
    IsScalarTower.of_algebraMap_smul fun r m ↦ by
      ext n
      exact IsScalarTower.algebraMap_smul K r (m.coeff n)
  exact ((PolynomialModule.eval x).restrictScalars R).comp
    (((PolynomialModule.map L (LinearMap.id : V →ₗ[K] V)).restrictScalars R).comp
      δ.mapCoeffs.toLinearMap)

omit [Algebra K L] [IsScalarTower K L V] in
@[simp] theorem coefficientEvalLinearMap_C (x : L) (δ : Derivation R K V) (a : K) :
    coefficientEvalLinearMap x δ (C a) = δ a := by
  simp [coefficientEvalLinearMap]

omit [Algebra K L] [IsScalarTower K L V] in
@[simp] theorem coefficientEvalLinearMap_X (x : L) (δ : Derivation R K V) :
    coefficientEvalLinearMap x δ X = 0 := by
  simp [coefficientEvalLinearMap]

/-- 係数導分の評価は、同じ評価写像による作用についてLeibniz則を満たす。 -/
theorem coefficientEvalLinearMap_leibniz (x : L) (δ : Derivation R K V) (f g : K[X]) :
    coefficientEvalLinearMap x δ (f * g) =
      aeval x f • coefficientEvalLinearMap x δ g +
        aeval x g • coefficientEvalLinearMap x δ f := by
  change (PolynomialModule.eval x) ((PolynomialModule.map L LinearMap.id)
    (δ.mapCoeffs (f * g))) = _
  rw [δ.mapCoeffs.leibniz, map_add, map_add, PolynomialModule.map_smul,
    PolynomialModule.map_smul, PolynomialModule.eval_smul, PolynomialModule.eval_smul]
  simp only [Polynomial.eval_map, Polynomial.aeval_def, coefficientEvalLinearMap,
    LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  rfl

end CoefficientEval

section Span

/-- 代数の生成元の導分の像は、全導分の像と同じ部分加群を生成する。 -/
theorem span_range_derivation_eq_span_of_adjoin_eq_top
    {R S V : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup V] [Module S V] [Module R V]
    (δ : Derivation R S V) (s : Set S) (hs : Algebra.adjoin R s = ⊤) :
    Submodule.span S (Set.range δ) = Submodule.span S (δ '' s) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ Algebra.adjoin R s := hs.symm ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | algebraMap r => simp
    | add x y _ _ hx hy => simpa using (Submodule.span S (δ '' s)).add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [δ.leibniz]
      exact (Submodule.span S (δ '' s)).add_mem
        (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ hx)
  · exact Submodule.span_mono (Set.image_subset_range _ _)

/-- 標数 p の代数への導分は p 乗を消す。 -/
theorem derivation_pow_char_eq_zero
    {R S V : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup V] [Module S V] [Module R V]
    (p : ℕ) [CharP S p] (δ : Derivation R S V) (x : S) : δ (x ^ p) = 0 := by
  rw [δ.leibniz_pow, ← Nat.cast_smul_eq_nsmul S, CharP.cast_eq_zero S p, zero_smul]

end Span

section Ideal

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M]

/-- 導分はイデアル冪の次数を高々一つ下げる。 -/
theorem derivation_mem_pow_smul (δ : Derivation R S M) (I : Ideal S) (n : ℕ)
    {x : S} (hx : x ∈ I ^ (n + 1)) : δ x ∈ I ^ n • (⊤ : Submodule S M) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ'] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb ↦ ?_) (fun a b ha hb ↦ ?_)
    · rw [δ.leibniz]
      apply Submodule.add_mem
      · rw [pow_succ', Submodule.mul_smul]
        exact Submodule.smul_mem_smul ha (ih hb)
      · exact Submodule.smul_mem_smul hb Submodule.mem_top
    · rw [map_add]
      exact Submodule.add_mem _ ha hb

/-- 非零イデアル内の元の微分は、分数体上で全ての微分と同じ部分空間を生成する。 -/
theorem span_derivation_ideal_eq_span_range
    {R S L V : Type*} [CommRing R] [CommRing S] [IsDomain S] [Field L]
    [Algebra R S] [Algebra S L] [IsFractionRing S L]
    [AddCommGroup V] [Module R V] [Module S V] [Module L V]
    [IsScalarTower S L V]
    (δ : Derivation R S V) (H : Ideal S) (hH : H ≠ ⊥) :
    Submodule.span L (δ '' (H : Set S)) = Submodule.span L (Set.range δ) := by
  classical
  apply le_antisymm
  · exact Submodule.span_mono (Set.image_subset_range _ _)
  · apply Submodule.span_le.mpr
    rintro _ ⟨b, rfl⟩
    have hex : ∃ x ∈ H, x ≠ 0 := by
      by_contra h
      apply hH
      apply le_antisymm ?_ bot_le
      intro x hx
      simpa using (show x = 0 by aesop)
    obtain ⟨x, hx, hx0⟩ := hex
    let N := Submodule.span L (δ '' (H : Set S))
    have hdx : δ x ∈ N := Submodule.subset_span ⟨x, hx, rfl⟩
    have hdbx : δ (b * x) ∈ N :=
      Submodule.subset_span ⟨b * x, H.mul_mem_left b hx, rfl⟩
    have hbdx : b • δ x ∈ N := by
      rw [← algebraMap_smul L b (δ x)]
      exact N.smul_mem _ hdx
    have hxdb : x • δ b ∈ N := by
      have := N.sub_mem hdbx hbdx
      simpa only [δ.leibniz, add_sub_cancel_left] using this
    have hmap : algebraMap S L x ≠ 0 :=
      fun h ↦ hx0 (IsFractionRing.injective S L (by simpa using h))
    have := N.smul_mem (algebraMap S L x)⁻¹ hxdb
    rw [← algebraMap_smul L x (δ b), smul_smul, inv_mul_cancel₀ hmap, one_smul] at this
    exact this

/-- 全微分が生成するなら、任意の非零イデアルの微分も生成する。 -/
theorem span_derivation_ideal_eq_top
    {R S L V : Type*} [CommRing R] [CommRing S] [IsDomain S] [Field L]
    [Algebra R S] [Algebra S L] [IsFractionRing S L]
    [AddCommGroup V] [Module R V] [Module S V] [Module L V]
    [IsScalarTower S L V]
    (δ : Derivation R S V) (H : Ideal S) (hH : H ≠ ⊥)
    (hδ : Submodule.span L (Set.range δ) = ⊤) :
    Submodule.span L (δ '' (H : Set S)) = ⊤ :=
  (span_derivation_ideal_eq_span_range δ H hH).trans hδ

/-- 有限個の指定ベクトルを、非零イデアル内の元の微分で摂動して独立にする。
係数体変更に必要な「元の選択」まで、一般線形代数と Leibniz 則から供給する。 -/
theorem exists_linearIndependent_derivation_perturbation
    {R S L V ι : Type*} [CommRing R] [CommRing S] [IsDomain S] [Field L]
    [Algebra R S] [Algebra S L] [IsFractionRing S L]
    [AddCommGroup V] [Module R V] [Module S V] [Module L V]
    [IsScalarTower S L V] [FiniteDimensional L V] [Fintype ι]
    (δ : Derivation R S V) (H : Ideal S) (hH : H ≠ ⊥)
    (hδ : Submodule.span L (Set.range δ) = ⊤)
    (b : ι → V) (hn : Fintype.card ι ≤ Module.finrank L V) :
    ∃ m : ι → S, (∀ i, m i ∈ H) ∧
      LinearIndependent L (fun i ↦ b i + δ (m i)) := by
  classical
  obtain ⟨w, hw, hind⟩ := exists_linearIndependent_add_of_span_eq_top
    (span_derivation_ideal_eq_top δ H hH hδ) b (by
      rw [Nat.card_eq_fintype_card, ← Module.finrank_eq_rank]
      exact_mod_cast hn)
  have hex (i : ι) : ∃ m ∈ H, δ m = w i := by
    rcases hw i with hzero | himage
    · exact ⟨0, H.zero_mem, by simp [← hzero]⟩
    · exact himage
  choose m hm hdm using hex
  refine ⟨m, hm, ?_⟩
  simpa only [hdm] using hind

end Ideal

end SerrePositivity
