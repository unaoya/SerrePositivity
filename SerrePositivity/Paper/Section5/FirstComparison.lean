module

public import SerrePositivity.IntersectionMultiplicity.Basic
public import Mathlib.Algebra.Ring.Action.Basic
public import SerrePositivity.PerfectComplex.Free.Support
public import SerrePositivity.PerfectComplex.Free.Euler
public import SerrePositivity.IntersectionMultiplicity.ResolutionEvaluation
public import SerrePositivity.Paper.Section3.NormComparison
public import SerrePositivity.LengthAlgebra.Core
public import SerrePositivity.CommutativeAlgebra.Length.CommonResidueField
public import SerrePositivity.IntersectionMultiplicity.Additivity
public import Mathlib.Algebra.CharP.Algebra

/-! # 第一のノルム比較（論文 Lemma 5.2）

## 概要

§5 の設定で `|G| · rank_{R/P} D · rank_{R/Q} E · χ^R(R/P, R/Q) = Σ_{σ ∈ G} c_σ`（`c_σ = Σ_i (-1)^i λ(Tor_i^R(C, E))`、`twistedEuler`）と各項の有限性を示す。

## 方針

有限拡大の階数倍、`E` の有限自由分解 `F` と `L = F ⊗_R D`（`D` の閉点に台を持つ完全複体）、`χ_D(L) = χ^R(D, E)` を経て、Lemma 3.5 を長さ代数に適用する（定義域の `m_T C` から `m_A C` への取り替えと、`v = 0` の有限性の補いは `normComparison_of_lengthAlgebra`）。形式的な移し替えは `firstComparison_of_complex`・`firstComparison_of_resolution`。

## 規約

ひねり `twist σ` は係数制限なので、係数拡大の言葉では `σ⁻¹` の構造射になる（最後に `σ ↦ σ⁻¹` で和を取り直す）。`Inputs/IntersectionTheory` の二つの未証明定理と Lemma 3.5 側の未証明結果への依存が残る。

## 使われ方

`Section5/Positivity`。
-/

@[expose] public noncomputable section

universe u

section FirstComparisonPart

open CategoryTheory

namespace SerrePositivity

/-- `σ ∈ G` でひねった構造射 `ι_σ : R → D →σ D → C`。論文 §5.1 の `ι_σ` で、`C` を `R` 代数とみる
やり方を `σ` ごとに変える。 -/
@[expose] noncomputable def twistedAlgebraMap (R D C G : Type u) [CommRing R] [CommRing D]
    [CommRing C] [Algebra R D] [Algebra D C] [Group G] [MulSemiringAction G D]
    (σ : G) : R →+* C :=
  (algebraMap D C).comp ((MulSemiringAction.toRingHom G D σ).comp (algebraMap R D))

/-- 論文 (5.2) の `c_σ = Σ_i (-1)^i λ(Tor_i^R(C, E))`：`C` を `ι_σ` で `R` 代数とみたときの `Tor` の
正規化 Euler 評価（`lambdaChi`）。 -/
@[expose] noncomputable def twistedEuler (R D E C G : Type u) [CommRing R] [CommRing D]
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

end FirstComparisonPart

section NormApplicationPart

open CategoryTheory Limits IsLocalRing
open scoped ENNReal

namespace SerrePositivity

/-- **長さ代数への Lemma 3.5 の適用**：正則局所環 `A` の正則パラメータ系 `z`、`A` 上有限で剰余体が同じ
局所環 `T`、`m_T C` 冪ねじれ加群上の正規化長さ `λ` で (3.9)（`hzero`、`hquot`、`v ≥ 1`）をみたすもの、
剰余標数 `p > 0`、`A` 上 `T` に作用する有限群 `G`（`Spec T → Spec A` は全射で幾何ファイバーで
推移的）について、`z` に台をもつ完全 `T` 複体 `L` の各共役 `g^*L` の係数拡大したホモロジーの `λ` は
有限で、共役和 `Σ_g χ_T(g^*L) = Σ_g χ_C(g^*L)` が成り立つ。完備性や生成的分離性など正規化基底の
条件は要らない。`λ` の定義域を `m_A C` に取り替え、`v = 0` を含む有限性を用意して `lemma_3_5` を
呼ぶ。Lemma 3.5 の入力（層 2 の `theorem_3_1_K0`、層 3a、`lemma_3_5a_lam_finite`）に依存する。 -/
theorem normComparison_of_lengthAlgebra
    (A T C : Type u) [CommRing A] [IsRegularLocalRing A] [CommRing T] [IsLocalRing T]
    [Algebra A T] [Module.Finite A T] [CommRing C] [Algebra T C] [Algebra A C] [IsScalarTower A T C]
    {e : ℕ} (z : Fin e → A) (he : 0 < e)
    (hz : Ideal.span (Set.range z) = maximalIdeal A) (hdim : ringKrullDim A = e)
    (hres : Function.Surjective ((residue T).comp (algebraMap A T)))
    (lam : NormalizedLength C ((maximalIdeal T).map (algebraMap T C)))
    (hzero : ∀ v : ℕ, 0 < v → ∀ i : ℕ, 0 < i →
      lam.len (koszulHomologySelf (fun j ↦ algebraMap A C (z j ^ v)) i) = 0)
    (hquot : ∀ v : ℕ, 0 < v →
      lam.len (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap A C (z j ^ v))) =
        ((v ^ e * Module.finrank A T : ℕ) : ℝ≥0∞))
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]
    (G : Type u) [Group G] [Fintype G] [MulSemiringAction G T] [SMulCommClass G A T]
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap A T)))
    (htrans : IsGeometricallyTransitive A T G)
    (L : PerfSupp T (algebraMap A T ∘ z)) :
    (∀ (g : G) (i : ℤ), lam.len ((baseChange (algebraMap T C) (twist g L.1)).homology i) ≠ ⊤) ∧
      (∑ g : G, chiOrd (twist g L.1)) =
        ∑ g : G, chiLam lam (algebraMap T C) (twist g L.1) := by
  let lam' := lam.restrictToBase A T
  have hfin : ∀ v j : ℕ,
      lam'.len (koszulHomologySelf (fun k ↦ algebraMap A C (z k ^ v)) j) ≠ ⊤ := by
    intro v j
    by_cases hv : v = 0
    · subst v
      have hx : (fun k : Fin e ↦ algebraMap A C (z k ^ 0)) = (fun _ ↦ (1 : C)) := by
        funext k
        simp
      rw [hx]
      obtain ⟨v, hv⟩ := isSupported_koszulComplex (fun _ : Fin e ↦ (1 : C))
      obtain ⟨H⟩ := hv ⟨0, he⟩
      have h := H.homologyMap_eq (-(j : ℤ))
      simp only [one_pow, one_smul, HomologicalComplex.homologyMap_id,
        HomologicalComplex.homologyMap_zero] at h
      have hz := (IsZero.iff_id_eq_zero _).mpr h
      have := ModuleCat.subsingleton_of_isZero hz
      rw [lam'.len_eq_zero_of_subsingleton]
      exact ENNReal.zero_ne_top
    · have hv' : 0 < v := Nat.pos_of_ne_zero hv
      cases j with
      | zero =>
        have eq0 := lam'.len_congr _ _
          (koszulComplex_homology_zero_equiv (fun k ↦ algebraMap A C (z k ^ v))).some
        have hfQ := ne_of_eq_of_ne (hquot v hv') (ENNReal.natCast_ne_top _)
        exact ne_of_eq_of_ne eq0 hfQ
      | succ j =>
        change lam.len _ ≠ ⊤
        rw [hzero v hv' (j + 1) (by omega)]
        exact ENNReal.zero_ne_top
  have ht1 : (fun j ↦ algebraMap A C (z j ^ 1)) = algebraMap A C ∘ z := by
    funext j
    simp
  have hkz : ∀ i : ℕ, 0 < i →
      lam'.len (koszulHomologySelf (algebraMap A C ∘ z) i) = 0 := by
    intro i hi
    have hv := hzero 1 one_pos i hi
    rwa [ht1] at hv
  have hq : lam'.len (C ⧸ Ideal.span (Set.range (algebraMap A C ∘ z))) =
      Module.finrank A T := by
    change lam.len _ = _
    have hv := hquot 1 one_pos
    rw [ht1] at hv
    simpa only [one_pow, one_mul] using hv
  have h := lemma_3_5 hz hdim hkz hq hfin hres
    p G hsurj htrans L
  exact ⟨h.2.1, h.2.2⟩

end SerrePositivity

end NormApplicationPart

section Lemma5_2Part

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
  obtain ⟨F, ⟨hF⟩, hbound, hfree, hfinite⟩ := regularResolution R E
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

end Lemma5_2Part
