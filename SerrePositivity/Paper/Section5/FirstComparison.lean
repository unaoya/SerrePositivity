module

public import SerrePositivity.IntersectionMultiplicity.Basic
public import Mathlib.Algebra.Ring.Action.Basic
public import SerrePositivity.PerfectComplex.Basic
public import SerrePositivity.PerfectComplex.OrdinaryEuler
public import SerrePositivity.IntersectionMultiplicity.ResolutionEvaluation

/-!
# 第一のノルム比較の組み立て

補題3.5が与える複体上の共役和の等式を、補題5.2の Tor と交点重複度の等式に移す。
`firstComparison_of_complex` は各評価の同一視を明示的に受け取り、
`firstComparison_of_resolution` は射影分解からそれらの一部を一般定理で導く。

係数制限によるひねりは、係数拡大として書くと逆元による係数構造に対応する。
最後に有限群の反転写像で和を取り直し、論文の `Σ_σ c_σ` にそろえる。
分解の存在や台の確認、実際の補題3.5の適用は `Paper/Lemma5_2.lean` で行う。
-/

public section

universe u

open CategoryTheory

namespace SerrePositivity

/-- 群の元でひねった係数構造 `R → D →σ D → C`。 -/
noncomputable def twistedAlgebraMap (R D C G : Type u) [CommRing R] [CommRing D]
    [CommRing C] [Algebra R D] [Algebra D C] [Group G] [MulSemiringAction G D]
    (σ : G) : R →+* C :=
  (algebraMap D C).comp ((MulSemiringAction.toRingHom G D σ).comp (algebraMap R D))

/-- 論文 (5.2) の `c_σ`。ひねった係数構造での Tor の正規化 Euler 評価。 -/
noncomputable def twistedEuler (R D E C G : Type u) [CommRing R] [CommRing D]
    [CommRing C] [Algebra R D] [Algebra D C] [AddCommGroup E] [Module R E]
    [Group G] [MulSemiringAction G D] {J : Ideal C} (lam : NormalizedLength C J)
    (σ : G) : ℝ :=
  lambdaChi lam (twistedAlgebraMap R D C G σ) E

variable {R D E C G : Type u} [CommRing R] [CommRing D] [CommRing C]
  [Algebra R D] [Algebra D C] [AddCommGroup E] [Module R E]
  [Group G] [Fintype G] [MulSemiringAction G D]
  (P Q : Ideal R) [Algebra (R ⧸ P) D] [Module (R ⧸ Q) E]
  {J : Ideal C} (lam : NormalizedLength C J)

/-- 補題5.2の結論を、複体上の共役和の比較と有限拡大の階数比較から組み立てる。
通常・正規化評価の同一視、Tor とホモロジーの線形同値、有限性は個別の引数として受け取る。 -/
theorem firstComparison_of_complex
    (L : CochainComplex (ModuleCat.{u} D) ℤ)
    (hfinite : ∀ (σ : G) (i : ℤ),
      lam.len ((baseChange (algebraMap D C) (twist σ L)).homology i) ≠ ⊤)
    (hnorm : (∑ σ : G, chiOrd (twist σ L)) =
      ∑ σ : G, chiLam lam (algebraMap D C) (twist σ L))
    (hOrd : ∀ σ : G, chiOrd (twist σ L) = (chi R D E : ℝ))
    (hLam : ∀ σ : G,
      chiLam lam (algebraMap D C) (twist σ L) = twistedEuler R D E C G lam σ⁻¹)
    (hTor : ∀ (σ : G) (i : ℕ),
      TorAlg (twistedAlgebraMap R D C G σ) i E ≃ₗ[C]
        ((baseChange (algebraMap D C) (twist σ⁻¹ L)).homology (-(i : ℤ))))
    (hRanks : chi R D E = (Module.finrank (R ⧸ P) D : ℤ) * Module.finrank (R ⧸ Q) E *
      chi R (R ⧸ P) (R ⧸ Q)) :
    (∀ (σ : G) (i : ℕ), lam.len (TorAlg (twistedAlgebraMap R D C G σ) i E) ≠ ⊤) ∧
      (Fintype.card G : ℝ) * Module.finrank (R ⧸ P) D * Module.finrank (R ⧸ Q) E *
        (chi R (R ⧸ P) (R ⧸ Q) : ℝ) = ∑ σ, twistedEuler R D E C G lam σ := by
  have hfiniteTor : ∀ (σ : G) (i : ℕ), lam.len (TorAlg (twistedAlgebraMap R D C G σ) i E) ≠ ⊤ := by
    intro σ i
    have hlen := lam.len_congr _ _ (hTor σ i)
    exact ne_of_eq_of_ne hlen (hfinite σ⁻¹ (-(i : ℤ)))
  have hsum : (∑ σ : G, twistedEuler R D E C G lam σ⁻¹) = ∑ σ : G, twistedEuler R D E C G lam σ :=
    Fintype.sum_equiv (Equiv.inv G) _ _ (fun _ ↦ rfl)
  have hcomparison : (Fintype.card G : ℝ) * (chi R D E : ℝ) =
      ∑ σ : G, twistedEuler R D E C G lam σ := by
    simp_rw [hOrd, hLam] at hnorm
    rw [hsum] at hnorm
    simpa using hnorm
  have hRanksReal : (chi R D E : ℝ) =
      (Module.finrank (R ⧸ P) D : ℝ) * Module.finrank (R ⧸ Q) E *
        (chi R (R ⧸ P) (R ⧸ Q) : ℝ) := by
    exact_mod_cast hRanks
  refine ⟨hfiniteTor, ?_⟩
  rw [← hcomparison, hRanksReal]
  ring

/-- `E′` の射影コチェイン分解から補題5.2の結論を組み立てる。
Tor との同一視、逆元を伴うひねりの評価、通常評価のひねり不変性は一般定理から導く。
共役和の比較、ひねる前の通常評価と交点重複度の一致、有限拡大の階数比較は引数として受け取る。 -/
theorem firstComparison_of_resolution
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hF : IsResolutionOf F (ModuleCat.of R E))
    (hfinite : ∀ (σ : G) (i : ℤ),
      lam.len ((baseChange (algebraMap D C)
        (twist σ (baseChange (algebraMap R D) F))).homology i) ≠ ⊤)
    (hnorm : (∑ σ : G, chiOrd (twist σ (baseChange (algebraMap R D) F))) =
      ∑ σ : G, chiLam lam (algebraMap D C)
        (twist σ (baseChange (algebraMap R D) F)))
    (hOrd : chiOrd (baseChange (algebraMap R D) F) = (chi R D E : ℝ))
    (hRanks : chi R D E = (Module.finrank (R ⧸ P) D : ℤ) * Module.finrank (R ⧸ Q) E *
      chi R (R ⧸ P) (R ⧸ Q)) :
    (∀ (σ : G) (i : ℕ), lam.len (TorAlg (twistedAlgebraMap R D C G σ) i E) ≠ ⊤) ∧
      (Fintype.card G : ℝ) * Module.finrank (R ⧸ P) D * Module.finrank (R ⧸ Q) E *
        (chi R (R ⧸ P) (R ⧸ Q) : ℝ) = ∑ σ, twistedEuler R D E C G lam σ := by
  apply firstComparison_of_complex P Q lam (baseChange (algebraMap R D) F) hfinite hnorm
    (fun σ ↦ (chiOrd_twist σ _).trans hOrd) ?_ ?_ hRanks
  · intro σ
    simpa only [twistedEuler, twistedAlgebraMap] using
      chiLam_twist_baseChange_resolution lam (algebraMap R D)
        (algebraMap D C) σ hF
  · intro σ i
    have key (g : G) : TorAlg (twistedAlgebraMap R D C G g⁻¹) i E ≃ₗ[C]
        ((baseChange (algebraMap D C)
          (twist g (baseChange (algebraMap R D) F))).homology (-(i : ℤ))) :=
      torAlgTwistBaseChangeEquiv (algebraMap R D) (algebraMap D C) g hF i
    have key' (g k : G) (hk : g⁻¹ = k) : TorAlg (twistedAlgebraMap R D C G k) i E ≃ₗ[C]
        ((baseChange (algebraMap D C)
          (twist g (baseChange (algebraMap R D) F))).homology (-(i : ℤ))) := by
      subst k
      exact key g
    exact key' σ⁻¹ σ (inv_inv σ)

end SerrePositivity
