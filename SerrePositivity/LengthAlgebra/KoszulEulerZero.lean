module

public import SerrePositivity.LengthAlgebra.ConeCompositionEuler
public import SerrePositivity.HomologicalAlgebra.KoszulModuleBounds

/-! # 高次の長さ消滅による Koszul Euler 評価の零次への還元

長さが零次以外で零なら、Euler 和は零次の長さの実数値だけになる。
この等式に零次の長さの有限性は不要である。
最後の元を正冪に替える Koszul 評価の倍率も、共通の錐合成の定理から導く。
-/

@[expose] public noncomputable section
universe u
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
