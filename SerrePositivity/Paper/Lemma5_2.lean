module

public import SerrePositivity.Paper.Section5.FirstComparison
public import SerrePositivity.Paper.Section5.NormApplication
public import SerrePositivity.IntersectionMultiplicity.FiniteExtension
public import SerrePositivity.IntersectionMultiplicity.ResolutionEvaluation
public import Mathlib.Algebra.CharP.Algebra

/-!
# Lemma 5.2：第一のノルム比較

## 概要

論文 Lemma 5.2 は、§5 の設定で交点重複度 `χ^R(R/P, R/Q)` を正規化長さによる量 `c_σ` の和で表す：

  `|G| · rank_{R/P} D · rank_{R/Q} E · χ^R(R/P, R/Q) = Σ_{σ ∈ G} c_σ`、

`c_σ = Σ_i (-1)^i λ(Tor_i^R(C, E))`（`C` の `R` 代数構造を `σ` でひねったもの、
`Paper/Section5/FirstComparison.lean` の `twistedEuler`）。各 `c_σ` の各項が有限であることも主張する
（`firstComparison`）。

## 証明

1. 有限拡大の階数倍（`IntersectionMultiplicity/FiniteExtension.lean`）：
   `χ^R(D, E) = rank_{R/P} D · rank_{R/Q} E · χ^R(R/P, R/Q)`。
2. `E` の有界有限自由分解 `F`（未証明定理 `Inputs.regularResolution`）をとり、`L = F ⊗_R D` とする。`D ⊗_R E` が
   有限長（`√(P + Q) = m_R` から）なので、`L` は `D` の閉点、すなわち `z` の像に台をもつ完全複体
   （`isPerfectSupported_baseChange_resolution`）。
3. `χ_D(L) = χ^R(D, E)`（`chiOrd_baseChange_resolution`。`R` と `D` の剰余体が同じことを使う）。
4. Lemma 3.5 を `A → D` と長さ代数 `(C, λ)` に適用して共役和の等式を得る
   （`Paper/Section5/NormApplication.lean`）。`A` の剰余標数が `p` であることは、`R` と `A` の剰余体が
   ともに `D` の剰余体と同型であること（`residueFieldEquiv_of_surjective`）から移す。
5. 以上を `firstComparison_of_resolution` で組み立てる。

## 仮定の扱い

有限代数 `D/(R/P)`、`E/(R/Q)`、正則局所環 `A`、群 `G`、長さ代数 `(C, λ)` を直接引数で受け取る。階数は
`Module.finrank` で表し、別の値との一致は仮定しない。基底の構成に用いる完備性・分離性、第二の
正規化基底や群は仮定に含めない。幾何的推移性は直接仮定する。二つの一般論の未証明定理
（`Inputs/IntersectionTheory.lean`）と、Lemma 3.5 側の未証明結果（層 2、層 3a、
`lemma_3_5a_lam_finite`）への依存は残る。
-/

public section

universe u

open CategoryTheory IsLocalRing
open scoped ENNReal

namespace SerrePositivity

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- **Lemma 5.2（第一のノルム比較）**：`|G| · rank_{R/P} D · rank_{R/Q} E · χ^R(R/P, R/Q) = Σ_σ c_σ` と、
各 `c_σ` の各項の有限性。仮定は、正則局所環 `A` の正則パラメータ系 `z`（`hz`、`hdimA`）、その `D` での
像が `D` の閉点を定めること（`hsupport`）、`A → D` と `R → D` が剰余体で全射（`hresA`、`hresR`）、
`Spec D → Spec A` の全射性と `G` の幾何的推移性（`hsurj`、`htrans`）、`E` の階数が正（`rankE`）、
次元の条件（`hPdim`、`hQdim`、`hsum`）、長さ代数の (3.9)（`hzero`、`hquot`）、剰余標数 `p`、
`√(P + Q) = m_R`（`hprimary`）。長さ代数の構成条件（完備性、分離性）は要らない。証明本体に `sorry` は
ないが、一般論の未証明定理と Lemma 3.5 の未証明結果に依存する。 -/
theorem firstComparison
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (A D E C G : Type u) [CommRing A] [IsRegularLocalRing A]
    [CommRing D] [IsLocalRing D] [Algebra R D] [Algebra (R ⧸ P) D]
    [IsScalarTower R (R ⧸ P) D] [Module.Finite (R ⧸ P) D]
    [CommRing E] [Algebra R E] [Algebra (R ⧸ Q) E]
    [IsScalarTower R (R ⧸ Q) E] [Module.Finite (R ⧸ Q) E]
    [Algebra A D] [Module.Finite A D]
    [CommRing C] [Algebra D C] [Algebra A C] [IsScalarTower A D C]
    [Group G] [Fintype G] [MulSemiringAction G D] [SMulCommClass G A D]
    {h l : ℕ} (z : Fin h → A) (hh : 0 < h)
    (hz : Ideal.span (Set.range z) = maximalIdeal A) (hdimA : ringKrullDim A = h)
    (hsupport : (Ideal.span (Set.range (algebraMap A D ∘ z))).radical = maximalIdeal D)
    (hresA : Function.Surjective ((residue D).comp (algebraMap A D)))
    (hresR : Function.Surjective ((residue D).comp (algebraMap R D)))
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap A D)))
    (htrans : IsGeometricallyTransitive A D G)
    (rankE : 0 < Module.finrank (R ⧸ Q) E)
    (hPdim : ringKrullDim (R ⧸ P) = h) (hQdim : ringKrullDim (R ⧸ Q) = l)
    (lam : NormalizedLength C ((maximalIdeal D).map (algebraMap D C)))
    (hzero : ∀ v : ℕ, 0 < v → ∀ i : ℕ, 0 < i →
      lam.len (koszulHomologySelf (fun j ↦ algebraMap A C (z j ^ v)) i) = 0)
    (hquot : ∀ v : ℕ, 0 < v →
      lam.len (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap A C (z j ^ v))) =
        ((v ^ h * Module.finrank A D : ℕ) : ℝ≥0∞))
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]
    (hsum : ringKrullDim (R ⧸ P) + ringKrullDim (R ⧸ Q) = ringKrullDim R)
    (hprimary : (P ⊔ Q).radical = maximalIdeal R) :
    (∀ (σ : G) (i : ℕ), lam.len (TorAlg (twistedAlgebraMap R D C G σ) i E) ≠ ⊤) ∧
      (Fintype.card G : ℝ) * Module.finrank (R ⧸ P) D * Module.finrank (R ⧸ Q) E *
        (chi R (R ⧸ P) (R ⧸ Q) : ℝ) = ∑ σ, twistedEuler R D E C G lam σ := by
  have : Module.Finite R D := Module.Finite.trans (R ⧸ P) D
  have : Module.Finite R E := Module.Finite.trans (R ⧸ Q) E
  have dimR : ((h + l : ℕ) : WithBot ℕ∞) = ringKrullDim R := by
    simpa only [hPdim, hQdim, Nat.cast_add] using hsum
  have hRanks := chi_finite_extensions P Q D E rankE hprimary h l hPdim hQdim dimR
  have htensor := length_tensorProduct_ne_top_of_annihilator P Q D E
    (quotient_action_annihilator P D) (quotient_action_annihilator Q E) hprimary
  obtain ⟨F, ⟨hF⟩, hbound, hfree, hfinite⟩ := Inputs.regularResolution R E
  let L := baseChange (algebraMap R D) F
  have hL : IsPerfectSupported (algebraMap A D ∘ z) L :=
    isPerfectSupported_baseChange_resolution E F hF hbound hfree hfinite htensor
      (algebraMap A D ∘ z) hsupport
  have hOrd : chiOrd L = (chi R D E : ℝ) :=
    chiOrd_baseChange_resolution E F hF hresR
  let eR := residueFieldEquiv_of_surjective (R := R) D hresR
  let eA := residueFieldEquiv_of_surjective (R := A) D hresA
  have : CharP (ResidueField A) p :=
    charP_of_injective_ringHom (f := (eR.trans eA.symm).toRingHom)
      (eR.trans eA.symm).injective p
  have hnorm := normComparison_of_lengthAlgebra A D C z hh hz hdimA hresA
    lam hzero hquot p G hsurj htrans ⟨L, hL⟩
  exact firstComparison_of_resolution P Q lam F hF hnorm.1 hnorm.2 hOrd hRanks

end SerrePositivity
