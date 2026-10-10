module

public import SerrePositivity.Paper.Section5.FirstComparison
public import SerrePositivity.Paper.Section5.NormApplication
public import SerrePositivity.IntersectionMultiplicity.FiniteExtension
public import SerrePositivity.IntersectionMultiplicity.ResolutionEvaluation
public import Mathlib.Algebra.CharP.Algebra

/-!
# 補題5.2：第一のノルム比較

有限代数 `D/(R/P)`、`E/(R/Q)`、正則局所環 `A`、群 `G`、長さ代数 `(C, λ)` を直接受け取る。
階数は `Module.finrank` で表し、別の値やそれとの一致を仮定しない。
`E` の有界有限自由分解を `D` に係数拡大し、閉点での台の条件を確認して補題3.5を適用する。

基底の構成に用いる完備性・分離性、第二の正規化基底や群は、この証明の仮定には含めない。
第一の群については幾何的推移性を直接仮定する。定理の結論は Tor の有限性と共役和の等式。
五つの一般論の入力クラスと、補題3.5側の未証明結果への依存は残っている。
-/

public section

universe u

open CategoryTheory IsLocalRing
open scoped ENNReal

namespace SerrePositivity

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]
  [Inputs.RegularResolution R] [Inputs.TorHomologicalAlgebra R] [Inputs.IntersectionAdditivity R]
  [Inputs.GenericBasis R] [Inputs.IntersectionVanishing R]

/-- 補題5.2。有限代数の階数、次元、パラメータ系、剰余体への全射、幾何的推移性を個別に仮定する。
`hPdim`・`hQdim` は商環の次元を自然数で指定する条件である。
`hsupport` は `z` の像で生成したイデアルが閉点を定める条件である。
長さ代数の構成条件は不要で、高次 Koszul ホモロジーの消滅 `hzero` と商の長さ `hquot` だけを用いる。
証明本体に `sorry` はないが、一般論の入力と補題3.5の未証明結果に依存する。 -/
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
    (rankD : 0 < Module.finrank (R ⧸ P) D) (rankE : 0 < Module.finrank (R ⧸ Q) E)
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
  have hRanks := chi_finite_extensions P Q D E rankD rankE hprimary h l hPdim hQdim dimR
  have htensor := length_tensorProduct_ne_top_of_annihilator P Q D E
    (quotient_action_annihilator P D) (quotient_action_annihilator Q E) hprimary
  obtain ⟨F, ⟨hF⟩, hbound, hfree, hfinite⟩ := Inputs.RegularResolution.resolution (R := R) E
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
