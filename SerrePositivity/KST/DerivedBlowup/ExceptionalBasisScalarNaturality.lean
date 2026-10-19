module

public import SerrePositivity.KST.DerivedBlowup.ExceptionalTransitionChart
public import SerrePositivity.KST.DerivedBlowup.FreeExteriorScalarNaturality

/-!
概要：KST v4 Lemma 3.6（pp.11–14）の例外因子の基底変換と係数変更の自然性。
方針：標準基底の係数を環射で送り、自己逆基底変換とその合成を比較する。
規約：原典の局所表示を明示的な半線形自由加群の計算で再構成する。
使われ方：例外因子の実際の有限重なり環を通る dg 遷移。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

variable {R S : Type u} [CommRing R] [CommRing S] {I : Type} [DecidableEq I]

/-- 概要：例外因子の関係式列は係数環の環射で保たれる。
方針：pivot とそれ以外で和・積の保存を使う。
規約：KST Lemma 3.6。使われ方：dg 係数変更後の微分の同定。 -/
theorem exceptionalRelationValue_scalarMap (φ : R →+* S) (a x : I → R) (i : I) :
    φ ∘ exceptionalRelationValue a x i = exceptionalRelationValue (φ ∘ a) (φ ∘ x) i := by
  funext j
  by_cases h : j = i <;> simp [exceptionalRelationValue, h]

/-- 概要：例外因子の自己逆基底変換は係数変更と可換。
方針：生成元上の二項変換を計算し、有限台関数の加法的帰納法で延長する。
規約：KST Lemma 3.6。使われ方：共通 Koszul 表示への比較の自然性。 -/
theorem exceptionalGeneratorMap_scalarMap (φ : R →+* S) (i : I) (x : I → R)
    (m : I →₀ R) :
    freeGeneratorScalarMap φ (exceptionalGeneratorMap i x m) =
      exceptionalGeneratorMap i (φ ∘ x) (freeGeneratorScalarMap φ m) := by
  change freeGeneratorScalarLinearMap φ (exceptionalGeneratorMap i x m) =
    exceptionalGeneratorMap i (φ ∘ x) (freeGeneratorScalarLinearMap φ m)
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add m n hm hn => simp only [map_add, hm, hn]
  | single j c =>
    rw [show Finsupp.single j c = c • Finsupp.single j (1 : R) by simp]
    simp only [map_smulₛₗ]
    congr 1
    change freeGeneratorScalarLinearMap φ (exceptionalGeneratorMap i x (Finsupp.single j 1)) =
      exceptionalGeneratorMap i (φ ∘ x) (freeGeneratorScalarMap φ (Finsupp.single j 1))
    rw [freeGeneratorScalarMap_single, map_one, exceptionalGeneratorMap_single,
      exceptionalGeneratorMap_single]
    by_cases hj : j = i
    · simp only [ite_eq_left hj]
      exact freeGeneratorScalarMap_single φ i 1 |>.trans (by rw [map_one])
    · simp only [ite_eq_right hj, map_sub, map_smulₛₗ]
      change φ (x j) • freeGeneratorScalarMap φ (Finsupp.single i 1) -
        freeGeneratorScalarMap φ (Finsupp.single j 1) = _
      rw [freeGeneratorScalarMap_single, freeGeneratorScalarMap_single, map_one]
      rfl

/-- 概要：例外因子の重なり基底変換は係数変更と可換。
方針：二つの自己逆基底変換の係数自然性を合成する。
規約：KST Lemma 3.6。使われ方：重なり環の変更を含む遷移。 -/
theorem exceptionalTransitionEquiv_scalarMap (φ : R →+* S) (i k : I) (x y : I → R)
    (m : I →₀ R) :
    freeGeneratorScalarMap φ (exceptionalTransitionEquiv i k x y m) =
      exceptionalTransitionEquiv i k (φ ∘ x) (φ ∘ y) (freeGeneratorScalarMap φ m) := by
  rw [exceptionalTransitionEquiv_apply, exceptionalGeneratorMap_scalarMap,
    exceptionalGeneratorMap_scalarMap, exceptionalTransitionEquiv_apply]

omit [DecidableEq I] in
/-- 概要：例外因子のチャート生成加群の包含は係数変更と可換。
方針：標準基底の係数変更を加法的帰納法で延長する。
規約：KST Lemma 3.6。使われ方：局所閉埋め込みの係数自然性。 -/
theorem exceptionalChartGeneratorInclusion_scalarMap (φ : R →+* S) (i : I)
    (m : ChartIndex i →₀ R) :
    freeGeneratorScalarMap φ (exceptionalChartGeneratorInclusion i m) =
      exceptionalChartGeneratorInclusion i (freeGeneratorScalarMap φ m) := by
  classical
  change freeGeneratorScalarLinearMap φ (exceptionalChartGeneratorInclusion i m) =
    exceptionalChartGeneratorInclusion i (freeGeneratorScalarLinearMap φ m)
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add m n hm hn => simp only [map_add, hm, hn]
  | single j c =>
    change freeGeneratorScalarMap φ (exceptionalChartGeneratorInclusion i (Finsupp.single j c)) =
      exceptionalChartGeneratorInclusion i (freeGeneratorScalarMap φ (Finsupp.single j c))
    rw [freeGeneratorScalarMap_single]
    simp only [exceptionalChartGeneratorInclusion, Finsupp.linearCombination_single]
    change freeGeneratorScalarLinearMap φ (c • Finsupp.single j.val 1) = _
    rw [map_smulₛₗ]
    change φ c • freeGeneratorScalarMap φ (Finsupp.single j.val 1) = _
    rw [freeGeneratorScalarMap_single, map_one]

end SerrePositivity.KST.DerivedBlowup
