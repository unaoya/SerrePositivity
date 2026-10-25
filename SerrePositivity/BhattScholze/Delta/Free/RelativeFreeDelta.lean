module

public import SerrePositivity.BhattScholze.Delta.Free.PolynomialDelta

/-! # 基底δ環上の相対自由δ環

基底のW₂切断を係数に用い、x_(s,n)を(x_(s,n),x_(s,n+1))へ送る切断を構成する。
pねじれを持つ基底にも適用できる、BS著者版Notation 2.8・Lemma 2.11の相対構成。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] (σ : Type v)

/-- 相対自由δ環の台環。変数x_(s,n)はδ^n(x_s)を表す。 -/
abbrev RelativeFreeDeltaRing := MvPolynomial (σ × ℕ) R

/-- 相対自由δ環の切断。係数には基底の切断を、変数には次のδ座標を用いる。 -/
def relativeFreeDeltaSection (D : DeltaStructure p R) :
    RelativeFreeDeltaRing (R := R) σ →+* WittTwo p (RelativeFreeDeltaRing (R := R) σ) :=
  polynomialDeltaSection (σ × ℕ) D (fun v ↦ MvPolynomial.X (v.1, v.2 + 1))

/-- 相対自由切断と第0座標射の合成は恒等写像。係数と変数上で確認する。 -/
theorem relativeFreeDeltaSection_projection (D : DeltaStructure p R) :
    (wittTwoProjection p (RelativeFreeDeltaRing (R := R) σ)).comp
      (relativeFreeDeltaSection σ D) = RingHom.id _ :=
  polynomialDeltaSection_projection (σ × ℕ) D _

/-- 相対自由δ構造。第0座標の切断条件を満たすW₂準同型から直接構成する。
基底のp正則性・非零性・完備性は要求しない。 -/
def relativeFreeDeltaStructure (D : DeltaStructure p R) :
    DeltaStructure p (RelativeFreeDeltaRing (R := R) σ) :=
  polynomialDeltaStructure (σ × ℕ) D (fun v ↦ MvPolynomial.X (v.1, v.2 + 1))

/-- 基底係数上のδは基底のδと一致する。 -/
@[simp] theorem relativeFreeDeltaStructure_delta_C (D : DeltaStructure p R) (r : R) :
    (relativeFreeDeltaStructure σ D).delta (MvPolynomial.C r) = MvPolynomial.C (D.delta r) := by
  exact polynomialDeltaStructure_delta_C (σ × ℕ) D _ r

/-- 相対自由δ環の生成元のδは次の座標。 -/
@[simp] theorem relativeFreeDeltaStructure_delta_X (D : DeltaStructure p R) (s : σ) (n : ℕ) :
    (relativeFreeDeltaStructure σ D).delta (MvPolynomial.X (s, n)) =
      MvPolynomial.X (s, n + 1) := by
  exact polynomialDeltaStructure_delta_X (σ × ℕ) D _ (s, n)

/-- 相対自由δ環への係数射はδ射。 -/
theorem relativeFreeDeltaStructure_C_isDeltaHom (D : DeltaStructure p R) :
    D.IsDeltaHom (relativeFreeDeltaStructure σ D) MvPolynomial.C :=
  polynomialDeltaStructure_C_isDeltaHom (σ × ℕ) D _

end SerrePositivity.BhattScholze
