module

public import SerrePositivity.HomologicalAlgebra.MinimalResolution
public import SerrePositivity.Asymptotic.RankQuotient
public import SerrePositivity.Asymptotic.NormalizedLimit
public import Mathlib.LinearAlgebra.StdBasis
public import SerrePositivity.Asymptotic.Completed
public import SerrePositivity.Asymptotic.SequenceKoszul
public import SerrePositivity.PerfectComplex.KoszulLength
public import SerrePositivity.LengthAlgebra.Perfect

/-! # 極小分解の切り詰めとランク商での消滅

## 概要

Betti 数が O(s) の加群列から、極小分解を項ごとに切り詰めた共通振幅 [-l, 0] の自由複体の列を作る（零次の階数公式と極小性を保つ）。ランク商でのスカラーの零作用と Koszul ホモロジー長の正規化超極限から、対象としての消滅、Euler 評価の第零次への集中、全射による下界を得る。

## 方針

共通の反復錐定理を使う。元の複体の列への一様な台は仮定せず、Koszul 複体の列自身の一様な台を使う。

## 規約

論文の結果を使う極小分解の部分（MinimalSupport など）は Paper/Section4/RankLowerBound に置く。

## 使われ方

Paper/Section4 の下界と §5。
-/

@[expose] public noncomputable section

universe u

section MinimalResolutionFamilyPart

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

end MinimalResolutionFamilyPart

section RankVanishingPart

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Filter

variable {R : Type u} [CommRing R] [Nontrivial R] {s : ℕ → ℕ} {J : Ideal R}
  (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (z : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ i, lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology i) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

omit [Nontrivial R] in
/-- `z` の `v` 乗を自然数で添字づけた Koszul 塔のスカラー列。`e` 以上では `0`。 -/
def koszulPowScalars (v : ℕ) : ℕ → R := LengthAlgebra.koszulScalars (fun j ↦ z j ^ v)

omit [Nontrivial R] in
lemma koszulPowScalars_fin (v : ℕ) :
    (fun j : Fin e ↦ koszulPowScalars z v j) = fun j ↦ z j ^ v :=
  funext fun j ↦ LengthAlgebra.koszulScalars_fin _ j

omit [Nontrivial R] in
lemma koszulPowScalars_of_lt (v j : ℕ) (hj : j < e) :
    koszulPowScalars z v j = z ⟨j, hj⟩ ^ v := by
  simp [koszulPowScalars, LengthAlgebra.koszulScalars, hj]

omit [Nontrivial R] in
/-- `z^v` の零作用は、塔のスカラー列の零作用。 -/
lemma koszulPowScalars_smul_zero {D : Type*} [Category* D] [Preadditive D] [Linear R D]
    (X : D) (v : ℕ) (hx : ∀ j, z j ^ v • 𝟙 X = 0) :
    ∀ j < e, koszulPowScalars z v j • 𝟙 X = 0 := fun j hj ↦ by
  rw [koszulPowScalars_of_lt z v j hj]
  exact hx ⟨j, hj⟩

section tower

variable (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
  (h : scalarSupported z (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)))
  (v : ℕ)

set_option maxHeartbeats 800000 in
-- 支持部分圏と二段階の商を含む型の比較に余裕を与える。
/-- Koszul 塔の頂上の Betti 数は、各段の実際の Koszul ホモロジー長の正規化超極限。 -/
lemma completedRankBetti_koszulTower_top (hv : 0 < v) (i : ℤ) :
    completedRankBetti lam hfg z hJ hfin U hU hs
      (sequenceKoszulTowerObj completedSequenceFunctor z (koszulPowScalars z v) K hK h e) i =
      normalizedLimit U s (fun t ↦ (lam.len
        ((koszulComplexOn (fun j ↦ z j ^ v) ((evaluateComplex t).obj K)).homology i)).toReal) := by
  have huni : supportedSequence z
      (sequenceHomotopyObj (sequenceKoszul (fun j : Fin e ↦ koszulPowScalars z v j) K)
        (sequenceKoszul_bounded _ K hK)) := by
    rw [koszulPowScalars_fin]
    exact sequenceKoszul_pow_supported z v hv K hK
  have he := completedRankBetti_complex z lam hfg hJ hfin U hU hs
    (sequenceKoszul (fun j : Fin e ↦ koszulPowScalars z v j) K) (sequenceKoszul_bounded _ K hK)
    huni (sequenceKoszulTowerObj completedSequenceFunctor z (koszulPowScalars z v)
      K hK h e).property i
  refine he.trans (congrArg (normalizedLimit U s) (funext fun t ↦ ?_))
  rw [koszulPowScalars_fin]
  exact congrArg ENNReal.toReal (lam.len_congr _ _
    (((HomologicalComplex.homologyFunctor _ _ i).mapIso
      (evaluateSequenceKoszulIso (fun j ↦ z j ^ v) K t)).toLinearEquiv))

set_option maxHeartbeats 800000 in
-- 支持部分圏と二段階の商を含む型の比較に余裕を与える。
/-- (Supp) と (Kosₘ) から得られるランク商での消滅。
振幅は Koszul ホモロジー長の超極限で確認すればよい。共通定理 `iteratedZeroCone_vanishing` の適用。 -/
theorem completedRankHomology_vanishing_of_koszul (hv : 0 < v)
    (hx : ∀ j, z j ^ v • 𝟙 (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)) = 0)
    (a b : ℤ)
    (hKos : ∀ q, q < a ∨ b < q → normalizedLimit U s (fun t ↦ (lam.len
      ((koszulComplexOn (fun j ↦ z j ^ v) ((evaluateComplex t).obj K)).homology q)).toReal) = 0)
    (q : ℤ) (hq : q < a + e ∨ b < q) :
    IsZero ((completedRankHomology lam hfg z hJ hfin U hU hs q).obj
      (completedComplexObj z K hK h)) := by
  let X := sequenceKoszulTowerObj completedSequenceFunctor z (koszulPowScalars z v) K hK h
  let H := completedRankHomology lam hfg z hJ hfin U hU hs 0
  have hv' := sequenceKoszulTower_vanishing completedSequenceFunctor z (koszulPowScalars z v)
    K hK h H e (koszulPowScalars_smul_zero z _ v hx) a b (fun i hi ↦ ?_) q hq
  · exact hv'.of_iso
      ((completedRankHomologyShiftNatIso lam hfg z hJ hfin U hU hs q).app (X 0)).symm
  · apply IsZero.of_iso _
      ((completedRankHomologyShiftNatIso lam hfg z hJ hfin U hU hs i).app (X e))
    apply (lengthQuotientValue_eq_zero_iff lam s U hU hs _).mp
    exact (completedRankBetti_koszulTower_top lam hfg z hJ hfin U hU hs K hK h v hv i).trans
      (hKos i hi)

set_option maxHeartbeats 800000 in
-- 支持部分圏と二段階の商を含む型の比較に余裕を与える。
/-- 振幅 `[-e, 0]` では、Euler 評価は実際の Koszul 第零ホモロジーの正規化極限。
共通定理 `iteratedZeroCone_euler_eq_length_zero` の適用。 -/
theorem completedRankEuler_eq_koszul_zero_limit_of_koszul (hv : 0 < v)
    (hx : ∀ j, z j ^ v • 𝟙 (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)) = 0)
    (hKos : ∀ q, q < -(e : ℤ) ∨ 0 < q → normalizedLimit U s (fun t ↦ (lam.len
      ((koszulComplexOn (fun j ↦ z j ^ v) ((evaluateComplex t).obj K)).homology q)).toReal) = 0) :
    completedRankEuler lam hfg z hJ hfin U hU hs (completedComplexObj z K hK h) =
      normalizedLimit U s (fun t ↦ (lam.len
        ((koszulComplexOn (fun j ↦ z j ^ v) ((evaluateComplex t).obj K)).homology 0)).toReal) := by
  let X := sequenceKoszulTowerObj completedSequenceFunctor z (koszulPowScalars z v) K hK h
  let T := sequenceKoszulTowerTriangle completedSequenceFunctor z (koszulPowScalars z v) K hK h
  let H := completedRankHomology lam hfg z hJ hfin U hU hs 0
  rw [completedRankEuler_eq_homologicalEuler]
  change homologicalEuler _ H (X 0) = _
  rw [iteratedZeroCone_euler_eq_length_zero X (fun k ↦ (T k).mor₂) (fun k ↦ (T k).mor₃) e
    (sequenceKoszulTower_zero_triangles completedSequenceFunctor z (koszulPowScalars z v) K hK h e
      (koszulPowScalars_smul_zero z _ v hx)) H
    (lengthQuotientValue lam s U hU hs) (lengthQuotientValue_iso lam s U hU hs)
    (fun Y hY ↦ (lengthQuotientValue_eq_zero_iff lam s U hU hs Y).mpr hY) (fun q hq ↦ ?_)]
  · exact (lengthQuotientValue_iso lam s U hU hs
      ((completedRankHomologyShiftNatIso lam hfg z hJ hfin U hU hs 0).app (X e))).trans
      (completedRankBetti_koszulTower_top lam hfg z hJ hfin U hU hs K hK h v hv 0)
  · apply IsZero.of_iso _
      ((completedRankHomologyShiftNatIso lam hfg z hJ hfin U hU hs q).app (X e))
    apply (lengthQuotientValue_eq_zero_iff lam s U hU hs _).mp
    exact (completedRankBetti_koszulTower_top lam hfg z hJ hfin U hU hs K hK h v hv q).trans
      (hKos q hq)

set_option maxHeartbeats 800000 in
-- 支持部分圏と二段階の商を含む型の比較に余裕を与える。
/-- Koszul 振幅と実際の第零次 Koszul ホモロジーからの全射による Euler 下界。
共通定理 `iteratedZeroCone_euler_lower_bound` の適用。 -/
theorem completedRankEuler_koszul_lower_bound (hv : 0 < v)
    (hx : ∀ j, z j ^ v • 𝟙 (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)) = 0)
    (hKos : ∀ q, q < -(e : ℤ) ∨ 0 < q → normalizedLimit U s (fun t ↦ (lam.len
      ((koszulComplexOn (fun j ↦ z j ^ v) ((evaluateComplex t).obj K)).homology q)).toReal) = 0)
    {Y : LengthSerreQuotient lam s U hU hs}
    (f : (completedRankHomology lam hfg z hJ hfin U hU hs 0).obj
      (completedComplexObj z (sequenceKoszul (fun j ↦ z j ^ v) K)
        (sequenceKoszul_bounded _ K hK)
        (sequenceKoszul_map_supported completedSequenceFunctor z _ K hK h)) ⟶ Y) [Epi f] :
    lengthQuotientValue lam s U hU hs Y ≤
      completedRankEuler lam hfg z hJ hfin U hU hs (completedComplexObj z K hK h) := by
  let X := sequenceKoszulTowerObj completedSequenceFunctor z (koszulPowScalars z v) K hK h
  let T := sequenceKoszulTowerTriangle completedSequenceFunctor z (koszulPowScalars z v) K hK h
  let H := completedRankHomology lam hfg z hJ hfin U hU hs 0
  have hf : X e = completedComplexObj z (sequenceKoszul (fun j ↦ z j ^ v) K)
      (sequenceKoszul_bounded _ K hK)
      (sequenceKoszul_map_supported completedSequenceFunctor z _ K hK h) := by
    change completedComplexObj z (sequenceKoszul (fun j : Fin e ↦ koszulPowScalars z v j) K) _ _ = _
    simp only [koszulPowScalars_fin]
  let f' : (H.shift (0 : ℤ)).obj (X e) ⟶ Y :=
    ((completedRankHomologyShiftNatIso lam hfg z hJ hfin U hU hs 0).app (X e)).hom ≫
      (H.mapIso (eqToIso hf)).hom ≫ f
  have : Epi f' := inferInstance
  rw [completedRankEuler_eq_homologicalEuler]
  change _ ≤ homologicalEuler _ H (X 0)
  apply iteratedZeroCone_euler_lower_bound X (fun k ↦ (T k).mor₂) (fun k ↦ (T k).mor₃) e
    (sequenceKoszulTower_zero_triangles completedSequenceFunctor z (koszulPowScalars z v) K hK h e
      (koszulPowScalars_smul_zero z _ v hx)) H
    (lengthQuotientValue lam s U hU hs) (lengthQuotientValue_iso lam s U hU hs)
    (lengthQuotientValue_add lam s U hU hs) (lengthQuotientValue_nonneg lam s U hU hs)
    (fun Y hY ↦ (lengthQuotientValue_eq_zero_iff lam s U hU hs Y).mpr hY) ?_ f'
  intro q hq
  apply IsZero.of_iso _ ((completedRankHomologyShiftNatIso lam hfg z hJ hfin U hU hs q).app (X e))
  apply (lengthQuotientValue_eq_zero_iff lam s U hU hs _).mp
  exact (completedRankBetti_koszulTower_top lam hfg z hJ hfin U hU hs K hK h v hv q).trans
    (hKos q hq)

end tower

omit [Nontrivial R] in
include hfg hJ in
/-- 各段の Koszul 消滅と項の振幅は、正規化超極限での (Kosₘ) を供給する。 -/
lemma sequenceKoszul_normalizedLimit_amplitude
    (v : ℕ)
    (hzero : ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (fun j ↦ z j ^ v) i) = 0)
    (K : CochainComplex (FreeSequence R s) ℤ) (a b : ℤ)
    (hbound : ∀ t q, q < a ∨ b < q → IsZero (((evaluateComplex t).obj K).X q))
    (q : ℤ) (hq : q < a ∨ b < q) : normalizedLimit U s (fun t ↦ (lam.len
      ((koszulComplexOn (fun j ↦ z j ^ v)
        ((evaluateComplex t).obj K)).homology q)).toReal) = 0 := by
  have hz (t : ℕ) : lam.len
      ((koszulComplexOn (fun j ↦ z j ^ v) ((evaluateComplex t).obj K)).homology q) = 0 :=
    lambdaHomology_koszul_projective_amplitude lam hfg (fun j ↦ z j ^ v)
      (le_radical_span_pow z hJ v) hzero ((evaluateComplex t).obj K)
      (fun q ↦ by
        change Module.Finite R (Fin ((K.X q).rank t) → R)
        infer_instance)
      (fun q ↦ by
        change Module.Projective R (Fin ((K.X q).rank t) → R)
        infer_instance) a b (hbound t) q hq
  simp only [hz, ENNReal.toReal_zero, normalizedLimit_zero]

/-- 環自身の Koszul 消滅と自由列の振幅から、商でのホモロジー消滅を得る。 -/
theorem completedRankHomology_vanishing
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : scalarSupported z (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)))
    (v : ℕ) (hv : 0 < v)
    (hx : ∀ j, z j ^ v • 𝟙 (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)) = 0)
    (hzero : ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (fun j ↦ z j ^ v) i) = 0)
    (a b : ℤ)
    (hbound : ∀ t q, q < a ∨ b < q → IsZero (((evaluateComplex t).obj K).X q))
    (q : ℤ) (hq : q < a + e ∨ b < q) :
    IsZero ((completedRankHomology lam hfg z hJ hfin U hU hs q).obj
      (completedComplexObj z K hK h)) :=
  completedRankHomology_vanishing_of_koszul lam hfg z hJ hfin U hU hs K hK h v hv hx a b
    (sequenceKoszul_normalizedLimit_amplitude lam hfg z hJ U v hzero K a b hbound) q hq

end SerrePositivity.Asymptotic

end RankVanishingPart

section RankMinimalLowerBoundPart

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits Filter

variable {R : Type u} [CommRing R] [Nontrivial R] {s : ℕ → ℕ} {J : Ideal R}
  (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (z : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ i, lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology i) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)
  (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
  (h : scalarSupported z (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)))
  (v : ℕ) (hv : 0 < v)
  (hx : ∀ j, z j ^ v • 𝟙 (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)) = 0)
  (hzero : ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (fun j ↦ z j ^ v) i) = 0)
  (hbound : ∀ t q, q < -(e : ℤ) ∨ 0 < q → IsZero (((evaluateComplex t).obj K).X q))

include hv hx hzero hbound

/-- 振幅 `[-e,0]` では、Euler 評価は実際の Koszul 第零ホモロジーの正規化極限。
環自身の Koszul 消滅と自由列の振幅から (Kosₘ) を確かめ、共通定理の適用
`completedRankEuler_eq_koszul_zero_limit_of_koszul` に渡す。 -/
theorem completedRankEuler_eq_koszul_zero_limit :
    completedRankEuler lam hfg z hJ hfin U hU hs (completedComplexObj z K hK h) =
      normalizedLimit U s (fun t ↦ (lam.len
        ((koszulComplexOn (fun j ↦ z j ^ v) ((evaluateComplex t).obj K)).homology 0)).toReal) :=
  completedRankEuler_eq_koszul_zero_limit_of_koszul lam hfg z hJ hfin U hU hs K hK h v hv hx
    (sequenceKoszul_normalizedLimit_amplitude lam hfg z hJ U v hzero K (-(e : ℤ)) 0 hbound)

/-- 極小性の具体的な全射から得られる Euler 下界。
イデアルは極大イデアルに限らず、微分の座標とパラメータの冪を含めばよい。 -/
theorem completedRankEuler_minimal_lower_bound
    (I : Ideal R) (hI : IsPowTorsion J (R ⧸ I))
    (hmin : ∀ t (m : Fin ((K.X (-1)).rank t) → R) j, (K.d (-1) 0 t m) j ∈ I)
    (hzI : ∀ j, z j ^ v ∈ I) :
    (lam.len (R ⧸ I)).toReal * normalizedLimit U s (fun t ↦ ((K.X 0).rank t : ℝ)) ≤
      completedRankEuler lam hfg z hJ hfin U hU hs (completedComplexObj z K hK h) := by
  rw [completedRankEuler_eq_koszul_zero_limit lam hfg z hJ hfin U hU hs K hK h
    v hv hx hzero hbound]
  have hle := normalizedLimit_mono U hU s hs
    (fun t ↦ (lam.len (R ⧸ I)).toReal * ((K.X 0).rank t : ℝ))
    (fun t ↦ (lam.len
      ((koszulComplexOn (fun j ↦ z j ^ v) ((evaluateComplex t).obj K)).homology 0)).toReal)
    ((K.X 0).rank_isBigO.const_mul_left _)
    (sequenceKoszulHomology_isBigO lam hfg _ (le_radical_span_pow z hJ v)
      (hfin v hv) K hK 0) (Eventually.of_forall fun t ↦ ?_)
  · rw [normalizedLimit_const_mul U hU s hs _ (K.X 0).rank_isBigO] at hle
    exact hle
  · have hb := lambdaHomology_koszul_zero_minimal_lower_bound lam hfg
      (fun j ↦ z j ^ v) (le_radical_span_pow z hJ v) ((evaluateComplex t).obj K)
      (fun q hq ↦ hbound t q (Or.inr hq)) I hI ((K.X 0).rank t) (Iso.refl _)
      (hmin t) hzI
    have hr := ENNReal.toReal_mono
      (sequenceKoszulHomology_ne_top lam hfg _ (le_radical_span_pow z hJ v)
        (hfin v hv) K hK t 0) hb
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_comm] using hr

/-- 正の生成元数の極限と商の正の長さから Euler 正値性を得る。 -/
theorem completedRankEuler_pos_of_minimal
    (I : Ideal R) (hI : IsPowTorsion J (R ⧸ I))
    (hmin : ∀ t (m : Fin ((K.X (-1)).rank t) → R) j, (K.d (-1) 0 t m) j ∈ I)
    (hzI : ∀ j, z j ^ v ∈ I)
    (hlen : 0 < (lam.len (R ⧸ I)).toReal)
    (hrank : 0 < normalizedLimit U s (fun t ↦ ((K.X 0).rank t : ℝ))) :
    0 < completedRankEuler lam hfg z hJ hfin U hU hs (completedComplexObj z K hK h) :=
  (mul_pos hlen hrank).trans_le
    (completedRankEuler_minimal_lower_bound lam hfg z hJ hfin U hU hs K hK h
      v hv hx hzero hbound I hI hmin hzI)

end SerrePositivity.Asymptotic

end RankMinimalLowerBoundPart
