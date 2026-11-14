module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDFrobeniusLift
public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism

/-!
# Frobenius を持つ分冪基底上の結晶 prism

## 概要
基底の Frobenius が分冪イデアルを (p) に送るとき、
p 正則な完備多項式分冪包に結晶 prism の構造を与える。

## 方針
既存の分冪包の Frobenius の持ち上げから δ 構造を取り、生成元を p とする。

## 規約
係数環の素数以外の自然数は単元。包の p 正則性を型に明記する。

## 使われ方
BS 著者版 Theorems 5.2・6.4 の小さい分冪模型への結晶の比較。
-/

public noncomputable section

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {k : Type u} [CommRing k]
variable (Dk : DeltaStructure p k) {J : Ideal k} (γ : DividedPowers J)
variable {σ : Type u} {K : Ideal (MvPolynomial σ k)} (E : CompletedPDEnvelopeData p γ K)
variable (hreg : Function.Injective (fun x : E.carrier => (p : E.carrier) * x))
variable (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : k))
variable (hφ : J.map Dk.frobeniusLift ≤ Ideal.span {(p : k)})

/-- p 正則な多項式分冪包を、変数の δ が零である結晶 prism にする。 -/
def pdEnvelopeCrystalline : OrientedPrism p E.carrier :=
  letI := E.isEnvelope.complete
  OrientedPrism.crystalline
    (exists_deltaStructure_of_pdPolynomial Dk γ E hreg hlocal hφ).choose hreg

/-- 小さい分冪包の結晶 prism の生成元は p。 -/
theorem pdEnvelopeCrystalline_generator :
    (pdEnvelopeCrystalline Dk γ E hreg hlocal hφ).generator = p := by
  unfold pdEnvelopeCrystalline
  rfl

/-- 基底の構造射は小さい分冪包の δ 構造を保つ。 -/
theorem pdEnvelopeCrystalline_base :
    Dk.IsDeltaHom (pdEnvelopeCrystalline Dk γ E hreg hlocal hφ).deltaStructure
      (algebraMap k E.carrier) :=
  (exists_deltaStructure_of_pdPolynomial Dk γ E hreg hlocal hφ).choose_spec.1

/-- 枠の各多項式変数の δ は零。 -/
theorem pdEnvelopeCrystalline_delta_X (i : σ) :
    (pdEnvelopeCrystalline Dk γ E hreg hlocal hφ).deltaStructure.delta
      (E.unit (MvPolynomial.X i)) = 0 :=
  (exists_deltaStructure_of_pdPolynomial Dk γ E hreg hlocal hφ).choose_spec.2.1 i

end SerrePositivity.BhattScholze.Prismatic
