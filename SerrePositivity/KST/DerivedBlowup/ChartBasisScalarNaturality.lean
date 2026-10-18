module

public import SerrePositivity.KST.DerivedBlowup.FreeExteriorScalarNaturality
public import SerrePositivity.KST.DerivedBlowup.KoszulBasis

/-!
概要：KST §3.1 のチャートの Koszul 基底変換は環射による係数変更と可換。
方針：規格化座標・標準生成元・基底変換の順に係数変更の公式を証明する。
規約：pivot 座標を表す単元も環射で送る。
使われ方：異なる有限重なり環を通るチャート dg 図式の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

variable {R S : Type u} [CommRing R] [CommRing S] {I : Type} [DecidableEq I]

omit [DecidableEq I] in
/-- 概要：規格化した座標は係数環の環射と可換。
方針：単元の逆元を環射で送り、乗法保存を使う。
規約：KST §3.1。使われ方：基底変換行列の係数比較。 -/
theorem normalizeCoordinates_scalarMap (φ : R →+* S) (x : I → R) (s : Rˣ) (j : I) :
    φ (normalizeCoordinates x s j) =
      normalizeCoordinates (φ ∘ x) (Units.map φ.toMonoidHom s) j := by
  change φ (x j * ↑s⁻¹) = φ (x j) * φ (↑s⁻¹)
  exact map_mul φ _ _

/-- 概要：pivot を零とした標準生成元は係数変更で保たれる。
方針：pivot とそれ以外に分け、標準基底の係数変更を計算する。
規約：KST §3.1。使われ方：Koszul 基底変換の係数自然性。 -/
theorem koszulGenerator_scalarMap (φ : R →+* S) (i j : I) :
    freeGeneratorScalarMap φ (koszulGenerator (B := R) i j) =
      koszulGenerator (B := S) i j := by
  by_cases h : j = i
  · subst j
    change freeGeneratorScalarLinearMap φ (koszulGenerator i i) = _
    simp
  · simp only [koszulGenerator, dite_eq_right h]
    rw [freeGeneratorScalarMap_single, map_one]

/-- 概要：チャートの Koszul 基底変換は係数変更と可換。
方針：標準基底で係数変更を計算し、有限台関数の加法的帰納法で延長する。
規約：KST §3.1。使われ方：基底変換と dg 係数変更の自然性。 -/
theorem koszulGeneratorMap_scalarMap (φ : R →+* S) (i k : I) (x : I → R) (s : Rˣ)
    (m : ChartIndex k →₀ R) :
    freeGeneratorScalarMap φ (koszulGeneratorMap i k x s m) =
      koszulGeneratorMap i k (φ ∘ x) (Units.map φ.toMonoidHom s)
        (freeGeneratorScalarMap φ m) := by
  change freeGeneratorScalarLinearMap φ (koszulGeneratorMap i k x s m) =
    koszulGeneratorMap i k (φ ∘ x) (Units.map φ.toMonoidHom s)
      (freeGeneratorScalarLinearMap φ m)
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add m n hm hn => simp only [map_add, hm, hn]
  | single j c =>
    rw [show Finsupp.single j c = c • Finsupp.single j (1 : R) by simp]
    simp only [map_smulₛₗ]
    congr 1
    simp only [koszulGeneratorMap, Finsupp.linearCombination_single, one_smul]
    change freeGeneratorScalarLinearMap φ
      (koszulGenerator i j.val - normalizeCoordinates x s j.val • koszulGenerator i k) =
      koszulGeneratorMap i k (φ ∘ x) (Units.map φ.toMonoidHom s)
        (freeGeneratorScalarMap φ (Finsupp.single j 1))
    rw [freeGeneratorScalarMap_single, map_one]
    simp only [koszulGeneratorMap, Finsupp.linearCombination_single, one_smul]
    rw [map_sub, map_smulₛₗ]
    change freeGeneratorScalarMap φ (koszulGenerator i j.val) -
      φ (normalizeCoordinates x s j.val) • freeGeneratorScalarMap φ (koszulGenerator i k) = _
    rw [koszulGenerator_scalarMap, koszulGenerator_scalarMap, normalizeCoordinates_scalarMap]

end SerrePositivity.KST.DerivedBlowup
