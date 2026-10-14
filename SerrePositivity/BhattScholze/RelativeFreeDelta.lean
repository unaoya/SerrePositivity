module

public import SerrePositivity.BhattScholze.DeltaSectionNaturality
public import Mathlib.Algebra.MvPolynomial.CommRing

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
  MvPolynomial.eval₂Hom ((wittTwoMap (p := p) MvPolynomial.C).comp D.sectionHom)
    (fun v ↦ TruncatedWittVector.mk p (fun i ↦
      if i = 0 then MvPolynomial.X v else MvPolynomial.X (v.1, v.2 + 1)))

/-- 相対自由切断と第0座標射の合成は恒等写像。係数と変数上で確認する。 -/
theorem relativeFreeDeltaSection_projection (D : DeltaStructure p R) :
    (wittTwoProjection p (RelativeFreeDeltaRing (R := R) σ)).comp
      (relativeFreeDeltaSection σ D) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, relativeFreeDeltaSection, MvPolynomial.eval₂Hom_C,
      wittTwoProjection_apply, wittTwoMap_coeff]
    rw [D.coeff_zero]
    rfl
  · intro v
    simp [relativeFreeDeltaSection]

/-- 相対自由δ構造。第0座標の切断条件を満たすW₂準同型から直接構成する。
基底のp正則性・非零性・完備性は要求しない。 -/
def relativeFreeDeltaStructure (D : DeltaStructure p R) :
    DeltaStructure p (RelativeFreeDeltaRing (R := R) σ) where
  sectionHom := relativeFreeDeltaSection σ D
  coeff_zero := by
    intro x
    have h := DFunLike.congr_fun (relativeFreeDeltaSection_projection σ D) x
    exact (wittTwoProjection_apply p _ _).symm.trans h

/-- 基底係数上のδは基底のδと一致する。 -/
@[simp] theorem relativeFreeDeltaStructure_delta_C (D : DeltaStructure p R) (r : R) :
    (relativeFreeDeltaStructure σ D).delta (MvPolynomial.C r) = MvPolynomial.C (D.delta r) := by
  simp [DeltaStructure.delta, relativeFreeDeltaStructure, relativeFreeDeltaSection]

/-- 相対自由δ環の生成元のδは次の座標。 -/
@[simp] theorem relativeFreeDeltaStructure_delta_X (D : DeltaStructure p R) (s : σ) (n : ℕ) :
    (relativeFreeDeltaStructure σ D).delta (MvPolynomial.X (s, n)) =
      MvPolynomial.X (s, n + 1) := by
  simp [DeltaStructure.delta, relativeFreeDeltaStructure, relativeFreeDeltaSection]

/-- 相対自由δ環への係数射はδ射。 -/
theorem relativeFreeDeltaStructure_C_isDeltaHom (D : DeltaStructure p R) :
    D.IsDeltaHom (relativeFreeDeltaStructure σ D) MvPolynomial.C := by
  intro r
  exact (relativeFreeDeltaStructure_delta_C σ D r).symm

end SerrePositivity.BhattScholze
