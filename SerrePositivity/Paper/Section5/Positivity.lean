module

public import SerrePositivity.Paper.Lemma5_2

/-!
# 核の場合の正値性（論文 §5.5）

補題5.2に必要な有限代数・パラメータ・長さを直接引数で受け取り、第一比較を証明する。
第二比較の評価 `b`、比較等式、正値性も個別の引数で渡す。
最後の算術は `chi_pos_of_comparisons` として、環や長さ代数から独立に証明する。

ここではデータの存在を一括で仮定するクラスを置かない。`core_of_inputs` は、指定した
対象と仮定が与えられた場合の正値性であり、対象の構成・第二比較の証明は別途必要である。
補題5.2の一般論の入力と未証明結果への依存も残る。
-/

public section

universe u

open IsLocalRing
open scoped ENNReal

namespace SerrePositivity

/-- 二つの有限和の比較と各項の正値性から、整数 `χ` の正値性を導く。
階数因子 `a, d` の正値性と添字集合の非空性だけを用いる最後の算術。 -/
theorem chi_pos_of_comparisons {G H : Type u} [Fintype G] [Nonempty G]
    [Fintype H] [Nonempty H] (a d : ℕ) (ha : 0 < a) (hd : 0 < d)
    (χ : ℤ) (c : G → ℝ) (b : G → H → ℝ)
    (hfirst : (Fintype.card G : ℝ) * a * d * (χ : ℝ) = ∑ σ, c σ)
    (hsecond : ∀ σ, (Fintype.card H : ℝ) * c σ = ∑ γ, b σ γ)
    (hpos : ∀ σ γ, 0 < b σ γ) : 0 < χ := by
  have hc (σ : G) : 0 < c σ := by
    have hs : 0 < ∑ γ, b σ γ := Finset.sum_pos (fun γ _ ↦ hpos σ γ) Finset.univ_nonempty
    rw [← hsecond σ] at hs
    have hcard : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
    exact (mul_pos_iff_of_pos_left hcard).mp hs
  have hs : 0 < ∑ σ, c σ := Finset.sum_pos (fun σ _ ↦ hc σ) Finset.univ_nonempty
  rw [← hfirst] at hs
  have hk : (0 : ℝ) < (Fintype.card G : ℝ) * a * d := by
    have : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
    positivity
  have : (0 : ℝ) < (χ : ℝ) := (mul_pos_iff_of_pos_left hk).mp hs
  exact_mod_cast this

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]
  [Inputs.RegularResolution R] [Inputs.TorHomologicalAlgebra R] [Inputs.IntersectionAdditivity R]
  [Inputs.GenericBasis R] [Inputs.IntersectionVanishing R]

/-- 補題5.2を適用し、第二比較の等式と正値性を合わせて交点重複度の正値性を導く。
第一比較の仮定を直接列挙し、第二比較の `b` と二つの性質を別の引数にする。
対象の存在を主張する定理ではなく、与えられた対象についての条件付きの結論である。 -/
theorem core_of_inputs
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (A D E C G : Type u) [CommRing A] [IsRegularLocalRing A]
    [CommRing D] [IsLocalRing D] [Algebra R D] [Algebra (R ⧸ P) D]
    [IsScalarTower R (R ⧸ P) D] [Module.Finite (R ⧸ P) D]
    [CommRing E] [Algebra R E] [Algebra (R ⧸ Q) E]
    [IsScalarTower R (R ⧸ Q) E] [Module.Finite (R ⧸ Q) E]
    [Algebra A D] [Module.Finite A D]
    [CommRing C] [Algebra D C] [Algebra A C] [IsScalarTower A D C]
    [Group G] [Finite G] [MulSemiringAction G D] [SMulCommClass G A D]
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
    (hprimary : (P ⊔ Q).radical = maximalIdeal R)
    (H : Type u) [Fintype H] [Nonempty H] (b : G → H → ℝ)
    (hsecond : ∀ σ, (Fintype.card H : ℝ) * twistedEuler R D E C G lam σ = ∑ γ, b σ γ)
    (hpos : ∀ σ γ, 0 < b σ γ) : 0 < chi R (R ⧸ P) (R ⧸ Q) := by
  let := Fintype.ofFinite G
  have hfirst := firstComparison P Q A D E C G z hh hz hdimA hsupport hresA hresR
    hsurj htrans rankD rankE hPdim hQdim lam hzero hquot p hsum hprimary
  exact chi_pos_of_comparisons (Module.finrank (R ⧸ P) D) (Module.finrank (R ⧸ Q) E)
    rankD rankE _ (twistedEuler R D E C G lam) b hfirst.2 hsecond hpos

end SerrePositivity
