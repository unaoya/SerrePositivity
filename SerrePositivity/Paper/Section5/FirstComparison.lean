module

public import SerrePositivity.IntersectionMultiplicity.Basic
public import Mathlib.Algebra.Ring.Action.Basic
public import SerrePositivity.PerfectComplex.Basic
public import SerrePositivity.PerfectComplex.OrdinaryEuler
public import SerrePositivity.IntersectionMultiplicity.ResolutionEvaluation

/-!
# 第一のノルム比較の組み立て（Lemma 5.2 の形式的部分）

## 概要

論文 Lemma 5.2 は、Lemma 3.5 が複体のレベルで与える共役和の等式 `Σ_σ χ_T(σ^*L) = Σ_σ χ_C(σ^*L)` を、
`Tor` と交点重複度の等式

  `|G| · rank_{R/P} D · rank_{R/Q} E · χ^R(R/P, R/Q) = Σ_σ c_σ`

（`c_σ = Σ_i (-1)^i λ(Tor_i^R(C, E))`、`R` の `C` 代数構造を `σ` でひねったもの、論文 (5.2)）に移す。
このファイルはその移し替えの形式的な部分を担う。

- `twistedAlgebraMap σ`：ひねった構造射 `R → D →σ D → C`。
- `twistedEuler σ`：論文の `c_σ`。
- `firstComparison_of_complex`：複体 `L` についての共役和の等式と、各評価の同一視（`χ_T(σ^*L) = χ^R(D, E)`、
  `χ_C(σ^*L) = c_{σ⁻¹}`、`Tor` とホモロジーの線形同値）、階数比較 `χ^R(D, E) = rank · rank · χ^R(R/P, R/Q)`
  を明示的に引数にとって結論を組み立てる。
- `firstComparison_of_resolution`：`E` の射影分解 `F` から `L = F ⊗_R D` をとり、上の同一視の一部
  （`Tor` との同一視、ひねりの評価、`χ_T` のひねり不変性）を
  `IntersectionMultiplicity/ResolutionEvaluation.lean` の一般定理で導く。

## 規約

ひねり `twist σ` は係数制限なので、係数拡大の言葉で書くと逆元 `σ⁻¹` による構造射に対応する
（`χ_C(σ^*L) = c_{σ⁻¹}`）。最後に `σ ↦ σ⁻¹` で和を取り直して論文の `Σ_σ c_σ` にそろえる。

分解の存在、台の確認、Lemma 3.5 の実際の適用は `Paper/Lemma5_2.lean`。
-/

public section

universe u

open CategoryTheory

namespace SerrePositivity

/-- `σ ∈ G` でひねった構造射 `ι_σ : R → D →σ D → C`。論文 §5.1 の `ι_σ` で、`C` を `R` 代数とみる
やり方を `σ` ごとに変える。 -/
noncomputable def twistedAlgebraMap (R D C G : Type u) [CommRing R] [CommRing D]
    [CommRing C] [Algebra R D] [Algebra D C] [Group G] [MulSemiringAction G D]
    (σ : G) : R →+* C :=
  (algebraMap D C).comp ((MulSemiringAction.toRingHom G D σ).comp (algebraMap R D))

/-- 論文 (5.2) の `c_σ = Σ_i (-1)^i λ(Tor_i^R(C, E))`：`C` を `ι_σ` で `R` 代数とみたときの `Tor` の
正規化 Euler 評価（`lambdaChi`）。 -/
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

/-- Lemma 5.2 の結論を、複体 `L` についての共役和の等式 `hnorm` と階数比較 `hRanks` から組み立てる。
各評価の同一視（`hOrd`：`χ_T(σ^*L) = χ^R(D, E)`、`hLam`：`χ_C(σ^*L) = c_{σ⁻¹}`、`hTor`：`Tor` と
ホモロジーの線形同値）と有限性 `hfinite` は個別の引数として受け取る。結論は、各 `c_σ` の各項が有限
であることと、`|G| · rank_{R/P} D · rank_{R/Q} E · χ^R(R/P, R/Q) = Σ_σ c_σ`。`hnorm` の両辺を
`hOrd`、`hLam` で書き換えると `|G| · χ^R(D, E) = Σ_σ c_{σ⁻¹}`、和を `σ ↦ σ⁻¹` で取り直し、`hRanks`
で `χ^R(D, E)` を展開する。 -/
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

/-- `E` の射影 cochain 分解 `F`（`IsResolutionOf F E`）から Lemma 5.2 の結論を組み立てる。`L = F ⊗_R D` に
ついて `firstComparison_of_complex` を使い、`Tor` との同一視（`torAlgTwistBaseChangeEquiv`）、ひねりの
評価 `χ_C(σ^*L) = c_{σ⁻¹}`（`chiLam_twist_baseChange_resolution`）、`χ_T` のひねり不変性
（`chiOrd_twist`）は一般定理から導く。共役和の等式 `hnorm`、ひねる前の `χ_T(L) = χ^R(D, E)`
（`hOrd`）、階数比較 `hRanks` は引数として受け取る。 -/
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
