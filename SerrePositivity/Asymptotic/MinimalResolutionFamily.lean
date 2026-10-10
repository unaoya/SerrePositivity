module

public import SerrePositivity.HomologicalAlgebra.MinimalTruncation
public import SerrePositivity.Asymptotic.AssembleComplex
public import SerrePositivity.Asymptotic.NormalizedLowerBound
public import Mathlib.LinearAlgebra.StdBasis

/-! # 極小分解を切り詰めた自由複体列

Betti 数が `O(s)` の加群列から、共通振幅 `[-l,0]` の自由複体列を構成する。
各段は極小分解の項ごとの切り詰めと鎖同型であり、零次の階数公式と極小性を保つ。
高次 Betti 数の `o(s)` がランクの `o(s)` になることも別に記録する。
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing Filter Asymptotics Topology
open scoped ENNReal

namespace SerrePositivity.Asymptotic

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- 標準自由加群の全座標がイデアルに入る条件は、任意の線形写像で保たれる。 -/
lemma map_coordinate_mem_ideal {a b : ℕ}
    (f : (Fin a → R) →ₗ[R] (Fin b → R)) (I : Ideal R)
    (x : Fin a → R) (hx : ∀ i, x i ∈ I) (j : Fin b) : f x j ∈ I := by
  classical
  have he : x = ∑ i, x i • Pi.single i (1 : R) := by
    ext i
    simp [Pi.single_apply]
  rw [he, map_sum]
  change (∑ i, f (x i • Pi.single i (1 : R))) j ∈ I
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  exact I.sum_mem (fun i _ ↦ I.mul_mem_right _ (hx i))

variable [IsLocalRing R] [IsNoetherianRing R]
variable (M : ℕ → FGModuleCat.{u} R) (l : ℕ) {s : ℕ → ℕ}

/-- 各次数の Betti 数の通常の漸近上界から、極小分解の階数の上界を得る。 -/
lemma minimal_rank_isBigO (i : ℕ)
    (h : (fun n ↦ ((Module.length R (TorModule R i (M n) (R ⧸ maximalIdeal R))).toNat : ℝ))
      =O[atTop] (fun n ↦ (s n : ℝ))) :
    (fun n ↦ (MinimalGenerators.rank (MinimalFreeResolution.syzygy (M n) i) : ℝ))
      =O[atTop] (fun n ↦ (s n : ℝ)) := by
  simpa only [MinimalFreeResolution.length_tor, ENat.toNat_natCast] using h

/-- 高次 Betti 数の無視できる増大度は、そのまま極小分解の項の階数に移る。 -/
lemma minimal_rank_isLittleO (i : ℕ)
    (h : (fun n ↦ ((Module.length R (TorModule R i (M n) (R ⧸ maximalIdeal R))).toNat : ℝ))
      =o[atTop] (fun n ↦ (s n : ℝ))) :
    (fun n ↦ (MinimalGenerators.rank (MinimalFreeResolution.syzygy (M n) i) : ℝ))
      =o[atTop] (fun n ↦ (s n : ℝ)) := by
  simpa only [MinimalFreeResolution.length_tor, ENat.toNat_natCast] using h

/-- 有限近似の Tor の正規化収束を、極小分解の階数の実数値の収束に移す。 -/
lemma minimal_rank_tendsto (i : ℕ) {L : ℝ≥0∞} (hL : L ≠ ⊤)
    (h : Tendsto (fun n ↦
      (Module.length R (TorModule R i (M n) (R ⧸ maximalIdeal R)) : ℝ≥0∞) / (s n : ℝ≥0∞))
      atTop (𝓝 L)) :
    Tendsto (fun n ↦ (MinimalGenerators.rank (MinimalFreeResolution.syzygy (M n) i) : ℝ) /
      (s n : ℝ)) atTop (𝓝 L.toReal) := by
  simpa [Function.comp_def, MinimalFreeResolution.length_tor] using
    (ENNReal.continuousAt_toReal hL).tendsto.comp h

/-- 有限な Tor の正規化極限から、分解の項のランクが `O(s)` であることを得る。 -/
lemma minimal_rank_isBigO_of_tendsto (i : ℕ) (hs : ∀ n, 0 < s n)
    {L : ℝ≥0∞} (hL : L ≠ ⊤)
    (h : Tendsto (fun n ↦
      (Module.length R (TorModule R i (M n) (R ⧸ maximalIdeal R)) : ℝ≥0∞) / (s n : ℝ≥0∞))
      atTop (𝓝 L)) :
    (fun n ↦ (MinimalGenerators.rank (MinimalFreeResolution.syzygy (M n) i) : ℝ))
      =O[atTop] (fun n ↦ (s n : ℝ)) := by
  apply isBigO_of_div_tendsto_nhds (Eventually.of_forall fun n hn ↦ ?_) L.toReal
    (minimal_rank_tendsto M i hL h)
  exact False.elim ((ne_of_gt (show (0 : ℝ) < s n by exact_mod_cast hs n)) hn)

/-- 高次 Tor の正規化極限が零なら、その次数の自由項のランクは `o(s)` である。 -/
lemma minimal_rank_isLittleO_of_tendsto_zero (i : ℕ) (hs : ∀ n, 0 < s n)
    (h : Tendsto (fun n ↦
      (Module.length R (TorModule R i (M n) (R ⧸ maximalIdeal R)) : ℝ≥0∞) / (s n : ℝ≥0∞))
      atTop (𝓝 0)) :
    (fun n ↦ (MinimalGenerators.rank (MinimalFreeResolution.syzygy (M n) i) : ℝ))
      =o[atTop] (fun n ↦ (s n : ℝ)) := by
  refine isLittleO_of_tendsto (fun n hn ↦
    False.elim ((ne_of_gt (show (0 : ℝ) < s n by exact_mod_cast hs n)) hn)) ?_
  simpa only [ENNReal.toReal_zero] using minimal_rank_tendsto M i (by simp) h

/-- 切り詰めた複体の各次数の階数は `O(s)` である。 -/
lemma truncated_rank_isBigO
    (h : ∀ i ≤ l,
      (fun n ↦ ((Module.length R (TorModule R i (M n) (R ⧸ maximalIdeal R))).toNat : ℝ))
        =O[atTop] (fun n ↦ (s n : ℝ))) (q : ℤ) :
    (fun n ↦ (Module.finrank R ((MinimalFreeResolution.truncated (M n) l).X q) : ℝ))
      =O[atTop] (fun n ↦ (s n : ℝ)) := by
  by_cases hq : q < -(l : ℤ) ∨ 0 < q
  · apply (isBigO_zero (fun n ↦ (s n : ℝ)) atTop).congr_left
    intro n
    have := ModuleCat.subsingleton_of_isZero (MinimalFreeResolution.truncated_isZero_X (M n) l q hq)
    simp only [Module.finrank_zero_of_subsingleton, Nat.cast_zero]
  · have he : q = -(((-q).toNat : ℕ) : ℤ) := by omega
    have hh (n : ℕ) : Module.finrank R ((MinimalFreeResolution.truncated (M n) l).X q) =
        MinimalGenerators.rank (MinimalFreeResolution.syzygy (M n) (-q).toNat) := by
      calc
        _ = Module.finrank R
            ((MinimalFreeResolution.truncated (M n) l).X (-(((-q).toNat : ℕ) : ℤ))) :=
          congrArg (fun q ↦ Module.finrank R ((MinimalFreeResolution.truncated (M n) l).X q)) he
        _ = _ := MinimalFreeResolution.truncated_finrank _ _ _ (by omega)
    simp_rw [hh]
    exact minimal_rank_isBigO M (-q).toNat (h _ (by omega))

/-- Lemma 5.5 の自由列の構成部分。指定振幅、全項の Betti 階数公式、零次の極小性を供給する。
ランク商での台の条件は、この定理ではまだ主張しない。 -/
theorem exists_minimal_truncated_sequence
    (h : ∀ i ≤ l,
      (fun n ↦ ((Module.length R (TorModule R i (M n) (R ⧸ maximalIdeal R))).toNat : ℝ))
        =O[atTop] (fun n ↦ (s n : ℝ))) :
    ∃ F : CochainComplex (FreeSequence R s) ℤ,
      (F.IsStrictlyGE (-(l : ℤ)) ∧ F.IsStrictlyLE 0) ∧
      (∀ n, Nonempty ((evaluateComplex n).obj F ≅ MinimalFreeResolution.truncated (M n) l)) ∧
      (∀ i ≤ l, ∀ n, ((F.X (-(i : ℤ))).rank n : ℕ∞) =
        Module.length R (TorModule R i (M n) (R ⧸ maximalIdeal R))) ∧
      ∀ n (x : Fin ((F.X (-1)).rank n) → R) (j : Fin ((F.X 0).rank n)),
        F.d (-1) 0 n x j ∈ maximalIdeal R := by
  let P (n : ℕ) := MinimalFreeResolution.truncated (M n) l
  let r (q : ℤ) (n : ℕ) := Module.finrank R ((P n).X q)
  have hr (q : ℤ) : (fun n ↦ (r q n : ℝ)) =O[atTop] (fun n ↦ (s n : ℝ)) :=
    truncated_rank_isBigO M l h q
  let e (n : ℕ) (q : ℤ) : ModuleCat.of R (Fin (r q n) → R) ≅ (P n).X q :=
    (Module.finBasis R ((P n).X q)).equivFun.toModuleIso.symm
  let F := assembleComplex P r hr e
  have hz (q : ℤ) (hq : q < -(l : ℤ) ∨ 0 < q) : IsZero (F.X q) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    funext n
    exact congrArg ModuleCat.Hom.hom
      (((MinimalFreeResolution.truncated_isZero_X (M n) l q hq).of_iso (e n q)).eq_of_src
        (𝟙 _) 0)
  refine ⟨F, ⟨(CochainComplex.isStrictlyGE_iff _ _).mpr (fun q hq ↦ hz q (.inl hq)),
    (CochainComplex.isStrictlyLE_iff _ _).mpr (fun q hq ↦ hz q (.inr hq))⟩,
    (fun n ↦ ⟨evaluateAssembleIso P r hr e n⟩), ?_, ?_⟩
  · intro i hi n
    exact MinimalFreeResolution.truncated_finrank_eq_length_tor (M n) l i hi
  · intro n x j
    let θ := MinimalFreeResolution.truncatedXIso (M n) l 0 (Nat.zero_le l)
    let y := (P n).d (-1) 0 ((e n (-1)).hom x)
    have hy : ∀ i, θ.hom y i ∈ maximalIdeal R :=
      MinimalFreeResolution.truncated_minimal (M n) l ((e n (-1)).hom x)
    have ht := map_coordinate_mem_ideal (θ.inv ≫ (e n 0).inv).hom
      (maximalIdeal R) (θ.hom y) hy j
    change (e n 0).inv.hom (θ.inv.hom (θ.hom.hom y)) j ∈ maximalIdeal R at ht
    have hθ : θ.inv.hom (θ.hom.hom y) = y := θ.toLinearEquiv.symm_apply_apply y
    change (e n 0).inv.hom (θ.inv.hom (θ.hom.hom y)) (j : Fin (r 0 n)) ∈ maximalIdeal R at ht
    rw [hθ] at ht
    exact ht

end SerrePositivity.Asymptotic
