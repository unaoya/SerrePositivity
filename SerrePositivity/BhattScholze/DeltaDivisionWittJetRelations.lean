module

public import SerrePositivity.BhattScholze.DeltaWittJetComparison
public import SerrePositivity.BhattScholze.DeltaDivisionIteratedRelations

/-! # 全有限δ除算関係式と切り詰めWitt積方程式の対応

任意通常射の下で比較し、終域のδ構造は要求しない。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {B : Type v} [CommRing B]

/-- 通常除算関係式の有限δjet消滅は、切り詰めWitt積方程式と同値。 -/
theorem deltaDivision_jets_zero_iff_witt_truncate_equation (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (q : A →+* B) (d x a : A) (N : ℕ) :
    (∀ i ≤ N, q (D.delta^[i] (d * x - a)) = 0) ↔
      WittVector.truncate (N + 1) (WittVector.map q (deltaWittGhostVector D d)) *
        WittVector.truncate (N + 1) (WittVector.map q (deltaWittGhostVector D x)) =
          WittVector.truncate (N + 1) (WittVector.map q (deltaWittGhostVector D a)) := by
  rw [deltaWittGhostVector_jets_zero_iff_truncate_map_zero D hp hg]
  let f := (WittVector.truncate (N + 1)).comp ((WittVector.map q).comp (deltaWittGhostRingHom D hg))
  change f (d * x - a) = 0 ↔ f d * f x = f a
  rw [map_sub, map_mul, sub_eq_zero]

/-- 任意族の有限反復除算関係式も、同じ深さのWitt積方程式族と同値。 -/
theorem deltaDivision_family_jets_zero_iff_witt_truncate_equations {σ : Type w}
    (D : DeltaStructure p A) (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (q : A →+* B) (d : A) (x a : σ → A) (N : ℕ) :
    (∀ s i, i ≤ N → q (D.delta^[i] (d * x s - a s)) = 0) ↔
      (∀ s, WittVector.truncate (N + 1) (WittVector.map q (deltaWittGhostVector D d)) *
        WittVector.truncate (N + 1) (WittVector.map q (deltaWittGhostVector D (x s))) =
          WittVector.truncate (N + 1) (WittVector.map q (deltaWittGhostVector D (a s)))) := by
  constructor
  · intro h s
    exact (deltaDivision_jets_zero_iff_witt_truncate_equation D hp hg q d (x s) (a s) N).mp (h s)
  · intro h s
    exact (deltaDivision_jets_zero_iff_witt_truncate_equation D hp hg q d (x s) (a s) N).mpr (h s)

/-- 相対自由δ環の実際の全有限反復関係式とWitt積方程式族の比較。 -/
theorem deltaDivisionIteratedRelations_zero_iff_witt_truncate_equations {σ : Type w}
    (D : DeltaStructure p A) (d : A) (a : σ → A)
    (hp : Function.Injective (fun f : RelativeFreeDeltaRing (R := A) σ =>
      (p : RelativeFreeDeltaRing (R := A) σ) * f))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (q : RelativeFreeDeltaRing (R := A) σ →+* B) (N : ℕ) :
    (∀ s i, i ≤ N → q (deltaDivisionIteratedRelation D d a s i) = 0) ↔
      (∀ s, WittVector.truncate (N + 1)
          (WittVector.map q (deltaWittGhostVector (relativeFreeDeltaStructure σ D)
            (MvPolynomial.C d))) *
        WittVector.truncate (N + 1)
          (WittVector.map q (deltaWittGhostVector (relativeFreeDeltaStructure σ D)
            (MvPolynomial.X (s, 0)))) =
        WittVector.truncate (N + 1)
          (WittVector.map q (deltaWittGhostVector (relativeFreeDeltaStructure σ D)
            (MvPolynomial.C (a s))))) := by
  exact deltaDivision_family_jets_zero_iff_witt_truncate_equations
    (relativeFreeDeltaStructure σ D) hp hg q (MvPolynomial.C d)
    (fun s => MvPolynomial.X (s, 0)) (fun s => MvPolynomial.C (a s)) N

end SerrePositivity.BhattScholze
