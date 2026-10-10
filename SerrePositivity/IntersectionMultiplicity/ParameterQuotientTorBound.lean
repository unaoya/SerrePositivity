module

public import SerrePositivity.IntersectionMultiplicity.ParameterQuotientTor
public import SerrePositivity.PerfectComplex.NormalizedEuler
public import SerrePositivity.HomologicalAlgebra.NullHomotopy
public import SerrePositivity.LengthAlgebra.PerfectVanishing
public import SerrePositivity.PerfectComplex.BaseChange

/-!
# パラメータ商の `Tor` の消滅（論文 Lemma 5.3 の後半）

## 概要

`R` 代数 `C`（`φ`）、`L` の長さ `d` 以下の有限自由分解、`x_j L = 0`（`j = 1, …, h`）とする。
`C` 上の正規化長さ `λ` について Koszul ホモロジーの評価 `λ(H_q(x^v; C)) = 0`（`q > 0`、`v ≥ 1`）が
成り立てば

  `λ(Tor_i^R(C, L)) = 0`（`i > d − h`）。

論文 Lemma 5.3 の `τ_i(L) = 0`（`i > l = d − h`）。

## 方針

`P_C = C ⊗ P_L` に対して、`LengthAlgebra.lambdaHomology_projective_vanishing` を適用する。
`x_j L = 0` から共通の正の冪が `P_C` 上で零ホモトピックとなることを確認し、
環自身の Koszul 消滅と分解の長さを具体的入力として渡す。
長さの商におけるホモロジーの消滅は、共通の反復錐定理から従う。
零作用の錐では消去指数が増えないため、以前の `2^h` 倍の指数は不要。

## 規約

複体は cochain（`ComplexShape.up ℤ`）。論文の homological 次数 `i` は cochain の `-i` 次。
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped ENNReal

namespace SerrePositivity

namespace TorBound

variable {C : Type u} [CommRing C]

/-- `a` がホモトピー圏で `X` 上の零写像として作用すること（`a • 𝟙 X` が零ホモトピック）。 -/
def Kills (a : C) (X : CochainComplex (ModuleCat.{u} C) ℤ) : Prop :=
  a • 𝟙 ((homotopyQuot C).obj X) = 0

end TorBound

/-! ## Lemma 5.3 の後半 -/

namespace ParamQuot

open TorBound

variable {R C : Type u} [CommRing R] [CommRing C] (φ : R →+* C) {h : ℕ} (x : Fin h → R)
  {J : Ideal C} (lam : NormalizedLength C J)

/-- `L` を消す `r` の冪は、`L` の射影分解の上で零ホモトピック。 -/
lemma exists_pow_kills_resolution (L : Type u) [AddCommGroup L] [Module R L]
    {d : ℕ} (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : IsResolutionOf P (ModuleCat.of R L))
    (hlen : ∀ i, i < -(d : ℤ) → IsZero (P.X i)) (r : R) (hr : ∀ l : L, r • l = 0) :
    ∃ w : ℕ, Nonempty (Homotopy (r ^ w • 𝟙 P) 0) := by
  refine exists_pow_nullHomotopy_of_homology_annihilated P r hP.projective
    ⟨-(d : ℤ), 0, fun i hi ↦ hi.elim (hlen i) (hP.isZero_X i)⟩ fun i ↦ ?_
  by_cases hi : i = 0
  · subst hi
    rw [← cancel_mono hP.homologyZeroIso.hom, zero_comp, Linear.smul_comp, Category.id_comp,
      ← Category.comp_id hP.homologyZeroIso.hom, ← Linear.comp_smul]
    convert comp_zero
    ext l
    exact hr l
  · exact (hP.isZero_homology i hi).eq_of_src _ _

/-- **Lemma 5.3 の後半**：`x_j L = 0`、`L` の長さ `d` 以下の有限自由分解、`J` は有限生成で
`J ⊆ √((x)C)`、Koszul ホモロジーの評価 `λ(H_q(x^v; C)) = 0`（`q, v > 0`）なら、
`i + h > d` で `λ(Tor_i^R(C, L)) = 0`。 -/
theorem len_torAlg_eq_zero (hfg : J.FG) (hJ : J ≤ (Ideal.span (Set.range (φ ∘ x))).radical)
    (hzero : ∀ v : ℕ, 0 < v → ∀ q : ℕ, 0 < q →
      lam.len (koszulHomologySelf (fun j ↦ φ (x j ^ v)) q) = 0)
    (L : Type u) [AddCommGroup L] [Module R L] (hL : ∀ j (l : L), x j • l = 0)
    {d : ℕ} (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : IsResolutionOf P (ModuleCat.of R L))
    (hfree : ∀ i, Module.Free R (P.X i)) (hfin : ∀ i, Module.Finite R (P.X i))
    (hlen : ∀ i, i < -(d : ℤ) → IsZero (P.X i)) (i : ℕ) (hi : d < i + h) :
    lam.len (TorAlg φ i L) = 0 := by
  let PC := baseChange φ P
  -- 各 `x_j` の冪が `P` 上で零ホモトピック。共通の冪 `w ≥ 1` をとる
  choose ws hws using fun j ↦ exists_pow_kills_resolution L P hP hlen (x j) (hL j)
  let w := Finset.univ.sup ws + 1
  have hw : 0 < w := Nat.succ_pos _
  have hkill : ∀ j, Kills (φ (x j) ^ w) PC := by
    intro j
    obtain ⟨H⟩ := hws j
    have hP' : (x j) ^ w • 𝟙 ((homotopyQuot R).obj P) = 0 :=
      pow_smul_id_eq_zero_of_le ((nonempty_homotopy_smul_id_zero_iff _ P).mp ⟨H⟩)
        ((Finset.le_sup (Finset.mem_univ j)).trans (Nat.le_succ _))
    obtain ⟨H'⟩ := (nonempty_homotopy_smul_id_zero_iff _ P).mpr hP'
    have H'' := (ModuleCat.extendScalars.{u, u, u} φ).mapHomotopy H'
    have eq1 : φ (x j) ^ w • 𝟙 PC =
        ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex _).map (x j ^ w • 𝟙 P) := by
      rw [← map_pow]
      exact (baseChange_smulId φ P (x j ^ w)).symm
    refine (nonempty_homotopy_smul_id_zero_iff _ PC).mp
      ⟨(Homotopy.ofEq eq1).trans (H''.trans (Homotopy.ofEq (Functor.map_zero _ _ _)))⟩
  -- (Supp)：共通の冪だけを使う。零作用の錐では追加の冪は不要。
  let c : Fin h → C := fun k ↦ φ (x k) ^ w
  have hJc : J ≤ (Ideal.span (Set.range c)).radical :=
    le_radical_span_pow (φ ∘ x) hJ w
  have hz : ∀ q : ℕ, 0 < q → lam.len (koszulHomologySelf c q) = 0 := by
    have heq : c = fun k ↦ φ (x k ^ w) := by funext k; simp [c]
    rw [heq]
    exact hzero w hw
  have hperfect : strictlyPerfectComplex R P := by
    refine ⟨⟨-(d : ℤ), 0, ?_, ?_⟩, fun q ↦ ?_⟩
    · rw [CochainComplex.isStrictlyGE_iff]
      exact hlen
    · rw [CochainComplex.isStrictlyLE_iff]
      exact hP.isZero_X
    · have := hfree q
      exact ⟨hfin q, Module.Projective.of_free⟩
  -- (Kos_d) の確認と共通の反復錐定理により消滅する。
  rw [lam.len_congr _ _ (torIsoCochain φ hP i).toLinearEquiv]
  exact LengthAlgebra.lambdaHomology_projective_vanishing lam hfg c hJc hz PC
    (strictlyPerfectComplex_baseChange φ P hperfect)
    (fun j ↦ (nonempty_homotopy_smul_id_zero_iff _ PC).mpr (hkill j))
    (-(d : ℤ)) 0
    (fun q hq ↦ (ModuleCat.extendScalars φ).map_isZero
      (hq.elim (hlen q) (hP.isZero_X q))) (-(i : ℤ)) (Or.inl (by omega))

end ParamQuot


end SerrePositivity
