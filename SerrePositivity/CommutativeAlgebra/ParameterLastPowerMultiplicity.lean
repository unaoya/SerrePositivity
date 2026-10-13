module

public import SerrePositivity.CommutativeAlgebra.KoszulMultiplicityProof
public import SerrePositivity.CommutativeAlgebra.KoszulFiniteLength
public import SerrePositivity.CommutativeAlgebra.ParameterLastPower
public import SerrePositivity.LengthAlgebra.ConeCompositionEuler

/-! # 最後のパラメータだけを冪にしたときの重複度

列の最後の座標を正の k 乗へ置き換えても根基は変わらない。
スカラー錐の合成に対する Euler 加法性と、証明済みの Koszul 重複度公式から
重複度の倍率 k を導く。全座標を同じ冪にする公式とは区別する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory Limits IsLocalRing
set_option backward.isDefEq.respectTransparency false

/-- 最後の座標だけを冪にした Koszul 複体は、前の列へのその冪のスカラー錐である。 -/
theorem koszulComplex_last_pow_eq {D : Type u} [CommRing D] {e : ℕ}
    (z : Fin (e + 1) → D) (k : ℕ) :
    koszulComplex (Fin.snoc (Fin.init z) (z (Fin.last e) ^ k)) =
      CochainComplex.mappingCone (smulId (z (Fin.last e) ^ k) (koszulComplex (Fin.init z))) := by
  rw [koszulComplex_succ]
  rw [Fin.snoc_last]
  apply congrArg (fun y : Fin e → D ↦
    CochainComplex.mappingCone (smulId (z (Fin.last e) ^ k) (koszulComplex y)))
  funext j
  exact Fin.snoc_castSucc _ _ j

/-- 最後のパラメータの k 乗による Koszul Euler 数の倍率は k。
前の列のホモロジーに有限長性を仮定せず、各正冪の錐の有限長性を使う。 -/
theorem chiOrd_koszul_last_pow (D : Type u) [CommRing D] [IsLocalRing D]
    [IsNoetherianRing D] {e : ℕ} (z : Fin (e + 1) → D)
    (hz : IsSystemOfParameters D z) (k : ℕ) (hk : 0 < k) :
    chiOrd (koszulComplex (Fin.snoc (Fin.init z) (z (Fin.last e) ^ k))) =
      (k : ℝ) * chiOrd (koszulComplex z) := by
  let P := koszulComplex (Fin.init z)
  let a := z (Fin.last e)
  have hb (n : ℕ) (_hn : 0 < n) : ∃ b₁ b₂ : ℤ, ∀ q,
      q < b₁ ∨ b₂ < q → IsZero ((Cone.cone (smulId (a ^ n) P)).X q) := by
    change ∃ b₁ b₂ : ℤ, ∀ q, q < b₁ ∨ b₂ < q →
      IsZero ((CochainComplex.mappingCone
        (smulId (z (Fin.last e) ^ n) (koszulComplex (Fin.init z)))).X q)
    rw [← koszulComplex_last_pow_eq z n]
    exact (isPerfectSupported_koszulComplex
      (Fin.snoc (Fin.init z) (z (Fin.last e) ^ n))).bounded
  have hl (n : ℕ) (hn : 0 < n) (q : ℤ) :
      (NormalizedLength.ordinary D).len ((Cone.cone (smulId (a ^ n) P)).homology q) ≠ ⊤ := by
    rw [NormalizedLength.ordinary_len]
    apply ENat.toENNReal_ne_top.mpr
    apply Module.length_ne_top_iff.mpr
    change IsFiniteLength D ((CochainComplex.mappingCone
      (smulId (z (Fin.last e) ^ n) (koszulComplex (Fin.init z)))).homology q)
    rw [← koszulComplex_last_pow_eq z n]
    exact isFiniteLength_koszulHomology_of_isSystemOfParameters D _ (hz.pow_last n hn) q
  have he := lambdaEuler_scalarCone_pow (NormalizedLength.ordinary D) P a hb
    (fun _ _ _ ↦ IsPowTorsion.bot) hl k hk
  change lambdaEuler (NormalizedLength.ordinary D)
      (CochainComplex.mappingCone (smulId (z (Fin.last e) ^ k) (koszulComplex (Fin.init z)))) =
    (k : ℝ) * lambdaEuler (NormalizedLength.ordinary D)
      (CochainComplex.mappingCone (smulId (z (Fin.last e)) (koszulComplex (Fin.init z)))) at he
  rw [← koszulComplex_last_pow_eq z k, ← koszulComplex_succ z,
    ← chiOrd_eq_lambdaEuler_ordinary, ← chiOrd_eq_lambdaEuler_ordinary] at he
  exact he

namespace HilbertSamuel

/-- 最後のパラメータだけを正の k 乗へ置き換えると、重複度は k 倍となる。
合成錐の共通 Euler 加法性と証明済みの Koszul 重複度公式から導く。 -/
theorem multiplicity_parameter_last_pow (D : Type u) [CommRing D] [IsLocalRing D]
    [IsNoetherianRing D] {e : ℕ} (z : Fin (e + 1) → D)
    (hz : IsSystemOfParameters D z) (k : ℕ) (hk : 0 < k) :
    multiplicity D (Ideal.span (Set.range (Fin.snoc (Fin.init z) (z (Fin.last e) ^ k)))) D =
      (k : ℚ) * multiplicity D (Ideal.span (Set.range z)) D := by
  have hreal : (multiplicity D
      (Ideal.span (Set.range (Fin.snoc (Fin.init z) (z (Fin.last e) ^ k)))) D : ℝ) =
      (k : ℝ) * (multiplicity D (Ideal.span (Set.range z)) D : ℝ) := by
    rw [KoszulMultiplicityProof.multiplicity_eq_chiOrd_koszul _ (hz.pow_last k hk),
      KoszulMultiplicityProof.multiplicity_eq_chiOrd_koszul z hz]
    exact chiOrd_koszul_last_pow D z hz k hk
  exact_mod_cast hreal

end HilbertSamuel

end SerrePositivity
