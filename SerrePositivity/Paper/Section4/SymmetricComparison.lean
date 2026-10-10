module

public import SerrePositivity.Paper.Section4.PaperK0Comparison
public import SerrePositivity.Asymptotic.PaperBaseChangeEvaluation
public import SerrePositivity.GroupTheory.ConjugateSum

/-! # 二つの長さ付き代数の対称なランク商比較

二つの係数環で Koszul Euler 数が一致すれば、基底の全対象で評価が一致する。
不変類の降下を加えると、共通の群論的比較から共役和が一致する。
群は評価元の K₀ にのみ作用し、係数代数・長さの同変性は要求しない。
-/

@[expose] public section

universe u

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Section4

open CategoryTheory IsLocalRing Filter Asymptotic

variable {A S C D : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [HasDerivedCategory (ModuleCat.{u} A)]
  [CommRing S] [Nontrivial S] [CommRing C] [Nontrivial C] [CommRing D] [Nontrivial D]
  (α : A →+* S) (φ : S →+* C) (ψ : S →+* D)
  {J : Ideal C} {I : Ideal D} (lam : NormalizedLength C J) (mu : NormalizedLength D I)
  (hfg : J.FG) (hIfg : I.FG) {e : ℕ} (z : Fin e → A)
  (hJ : J ≤ (Ideal.span (Set.range (φ ∘ α ∘ z))).radical)
  (hI : I ≤ (Ideal.span (Set.range (ψ ∘ α ∘ z))).radical)
  (hfin : LengthAlgebra.KoszulFinite lam (φ ∘ α ∘ z))
  (hfinD : LengthAlgebra.KoszulFinite mu (ψ ∘ α ∘ z))
  (hz : Ideal.span (Set.range z) = maximalIdeal A) (hK : IsKoszulResolution z)
  {s : ℕ → ℕ} (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

include hz hK

set_option maxHeartbeats 800000 in
-- 二段階の係数変更と、各係数環上の長さの局所化の型の比較に必要。
/-- 二段階の係数変更をした評価も、任意の Koszul Euler 数を係数とする。 -/
theorem paperBaseChangeEulerK0_eq_koszulEuler_mul :
    (paperBaseChangeEulerK0 φ (α ∘ z) lam hfg hJ hfin U hU hs).comp
      (TriangulatedK0.map (paperSupportedChangeRing α z)) =
        LengthAlgebra.koszulEuler lam (φ ∘ α ∘ z) •
          ordinaryPaperEulerK0 z (isArtinianRing_quotient_span_of_eq hz) U hU hs := by
  dsimp only [paperBaseChangeEulerK0]
  rw [AddMonoidHom.comp_assoc, paperSupportedChangeRingK0_comp]
  exact koszulPaperEulerK0_changeRing (φ.comp α) lam hfg z hJ hfin hz hK U hU hs

set_option maxHeartbeats 800000 in
-- 異なる二つの係数環の評価と、基底公式の比較に余裕を与える。
/-- 有限版と同じ対称な比較。全ての K₀ 類を扱い、係数環の高次消滅は仮定しない。 -/
theorem symmetricPaperEuler_conjSum_eq
    {G : Type*} [Group G] [Fintype G]
    [DistribMulAction G (TriangulatedK0 (paperSupportedRank (s := s) (α ∘ z)).FullSubcategory)]
    (hc : LengthAlgebra.koszulEuler lam (φ ∘ α ∘ z) =
      LengthAlgebra.koszulEuler mu (ψ ∘ α ∘ z))
    (hdesc : ∀ y : TriangulatedK0 (paperSupportedRank (s := s) (α ∘ z)).FullSubcategory,
      (∀ g : G, g • y = y) → ∃ (n : ℕ)
        (x : TriangulatedK0 (paperSupportedRank (s := s) z).FullSubcategory),
        0 < n ∧ n • y = TriangulatedK0.map (paperSupportedChangeRing α z) x)
    (y : TriangulatedK0 (paperSupportedRank (s := s) (α ∘ z)).FullSubcategory) :
    ∑ g : G, paperBaseChangeEulerK0 φ (α ∘ z) lam hfg hJ hfin U hU hs (g • y) =
      ∑ g : G, paperBaseChangeEulerK0 ψ (α ∘ z) mu hIfg hI hfinD U hU hs (g • y) := by
  have hC := paperBaseChangeEulerK0_eq_koszulEuler_mul α φ lam hfg z hJ hfin hz hK U hU hs
  have hD := paperBaseChangeEulerK0_eq_koszulEuler_mul α ψ mu hIfg z hI hfinD hz hK U hU hs
  have hbase := hC.trans ((congrArg (fun c : ℝ ↦ c •
    ordinaryPaperEulerK0 z (isArtinianRing_quotient_span_of_eq hz) U hU hs) hc).trans hD.symm)
  exact conjSum_eq (TriangulatedK0.map (paperSupportedChangeRing α z)) _ _
    (fun x ↦ DFunLike.congr_fun hbase x) hdesc y

end SerrePositivity.Section4
