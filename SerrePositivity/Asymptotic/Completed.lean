module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.Asymptotic.Karoubi
public import SerrePositivity.Asymptotic.Euler
public import SerrePositivity.CategoryTheory.IteratedCone
public import SerrePositivity.Asymptotic.SequenceKoszul
public import SerrePositivity.Asymptotic.RankBaseChange
public import SerrePositivity.CategoryTheory.ScalarSupport
public import SerrePositivity.CategoryTheory.Triangulated.VerdierKaroubi
public import Mathlib.CategoryTheory.Shift.Linear

/-! # 冪等完備化した商の上の評価

## 概要

台を持つ部分圏の商との比較を完全三角形と両立させて、冪等完備化した商の全対象にホモロジー長・Euler 評価・K₀ 上の準同型を与え、Koszul の係数公式、実際の一様支持の複体の列での評価、係数変更と台を与える。論文と同じ順序で作ったランク商（D_S = Kar(K^b)、N_S、P_S = Kar(D_S/N_S)）と、これまでの Kar(K^b/N) との線形三角同値（`PaperRankQuotient`）も与える。

## 方針

比較は三角関手の同値と冪等完備化の普遍性による。

## 規約

`PaperRankQuotient` は Asymptotic/DGVerdier/OrderSquare が使うので、論文の側（Paper/Section4）へは移さずここに置く。

## 使われ方

Paper/Section4、Asymptotic/DGVerdier、`Minimal`。
-/

@[expose] public noncomputable section

universe u

section CompletedRankEvaluationPart

set_option synthInstance.maxSize 1024

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
open CategoryTheory.Pretriangulated Filter

variable {R : Type u} [CommRing R] [Nontrivial R] {s : ℕ → ℕ} {J : Ideal R}
  (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (z : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ i, lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology i) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

instance completedRankHomology_isHomological (q : ℤ) :
    (completedRankHomology lam hfg z hJ hfin U hU hs q).IsHomological := by
  dsimp only [completedRankHomology]
  infer_instance

/-- 計算側の支持部分圏でも、各次数のホモロジーは第零次関手のシフトである。 -/
noncomputable def completedRankHomologyShiftNatIso (q : ℤ) :
    shiftFunctor _ q ⋙ completedRankHomology lam hfg z hJ hfin U hU hs 0 ≅
      completedRankHomology lam hfg z hJ hfin U hU hs q := by
  let E := (supportedKaroubiEquivalence (s := s) z).inverse
  let H := completedSupportedHomology lam hfg z hJ hfin U hU hs 0
  exact (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (E.commShiftIso q) H ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft E
      (completedSupportedHomologyShiftNatIso lam hfg z hJ hfin U hU hs q)

noncomputable instance completedRankHomology_shiftSequence :
    (completedRankHomology lam hfg z hJ hfin U hU hs 0).ShiftSequence ℤ :=
  Functor.ShiftSequence.tautological _ ℤ

/-- 既存の交代和は共通の Euler 評価に一致する。 -/
lemma completedRankEuler_eq_homologicalEuler
    (X : (supportedCompletedRankQuotient (s := s) z).FullSubcategory) :
    completedRankEuler lam hfg z hJ hfin U hU hs X =
      homologicalEuler (lengthQuotientValue lam s U hU hs)
        (completedRankHomology lam hfg z hJ hfin U hU hs 0) X := by
  unfold completedRankEuler completedSupportedEuler homologicalEuler
  simp only [zsmul_eq_mul]
  congr 1
  funext q
  congr 1
  exact (lengthQuotientValue_iso lam s U hU hs
    ((completedRankHomologyShiftNatIso lam hfg z hJ hfin U hU hs q).app X)).symm

/-- 共通 Euler 評価に使うシフト列は、完備化後も各対象で有界である。 -/
lemma completedRankHomology_shift_bounded
    (X : (supportedCompletedRankQuotient (s := s) z).FullSubcategory) :
    ∃ a b : ℤ, ∀ q, q < a ∨ b < q →
      IsZero (((completedRankHomology lam hfg z hJ hfin U hU hs 0).shift q).obj X) := by
  obtain ⟨a, b, hab⟩ := completedRankHomology_bounded lam hfg z hJ hfin U hU hs X
  exact ⟨a, b, fun q hq ↦ (hab q hq).of_iso
    ((completedRankHomologyShiftNatIso lam hfg z hJ hfin U hU hs q).app X)⟩

set_option maxHeartbeats 800000 in
-- 二重の商圏と同値の逆関手を含む型の簡約に余裕を与える。
/-- 全支持対象上の Euler 評価は標準的な完全三角形に関して加法的。 -/
lemma completedRankEuler_triangle
    (T : Triangle (supportedCompletedRankQuotient (s := s) z).FullSubcategory)
    (hT : T ∈ distTriang _) :
    completedRankEuler lam hfg z hJ hfin U hU hs T.obj₂ =
      completedRankEuler lam hfg z hJ hfin U hU hs T.obj₁ +
        completedRankEuler lam hfg z hJ hfin U hU hs T.obj₃ := by
  simp only [completedRankEuler_eq_homologicalEuler]
  exact homologicalEuler_triangle (lengthQuotientValue lam s U hU hs)
    (lengthQuotientValue_iso lam s U hU hs) (lengthQuotientValue_add lam s U hU hs)
    (completedRankHomology lam hfg z hJ hfin U hU hs 0)
    (fun X hX ↦ (lengthQuotientValue_eq_zero_iff lam s U hU hs X).mpr hX)
    (completedRankHomology_shift_bounded lam hfg z hJ hfin U hU hs) T hT

lemma completedRankEuler_iso
    {X Y : (supportedCompletedRankQuotient (s := s) z).FullSubcategory} (i : X ≅ Y) :
    completedRankEuler lam hfg z hJ hfin U hU hs X =
      completedRankEuler lam hfg z hJ hfin U hU hs Y :=
  completedSupportedEuler_iso lam hfg z hJ hfin U hU hs
    ((supportedKaroubiEquivalence z).inverse.mapIso i)

/-- 商の完備化の支持部分圏の K₀ 上に定義される Euler 評価。 -/
noncomputable def completedRankEulerK0 :
    TriangulatedK0 (supportedCompletedRankQuotient (s := s) z).FullSubcategory →+ ℝ :=
  homologicalEulerK0 (lengthQuotientValue lam s U hU hs)
    (lengthQuotientValue_iso lam s U hU hs) (lengthQuotientValue_add lam s U hU hs)
    (completedRankHomology lam hfg z hJ hfin U hU hs 0)
    (fun X hX ↦ (lengthQuotientValue_eq_zero_iff lam s U hU hs X).mpr hX)
    (completedRankHomology_shift_bounded lam hfg z hJ hfin U hU hs)

@[simp] lemma completedRankEulerK0_mk
    (X : (supportedCompletedRankQuotient (s := s) z).FullSubcategory) :
    completedRankEulerK0 lam hfg z hJ hfin U hU hs (TriangulatedK0.mk X) =
      completedRankEuler lam hfg z hJ hfin U hU hs X := by
  rw [completedRankEulerK0, homologicalEulerK0_mk, completedRankEuler_eq_homologicalEuler]

/-- 商の完備化で支持される対象の第 q 次ホモロジーの非負な実数値。 -/
noncomputable def completedRankBetti
    (X : (supportedCompletedRankQuotient (s := s) z).FullSubcategory) (q : ℤ) : ℝ :=
  lengthQuotientValue lam s U hU hs
    ((completedRankHomology lam hfg z hJ hfin U hU hs q).obj X)

lemma completedRankBetti_nonneg
    (X : (supportedCompletedRankQuotient (s := s) z).FullSubcategory) (q : ℤ) :
    0 ≤ completedRankBetti lam hfg z hJ hfin U hU hs X q := lengthQuotientValue_nonneg ..

lemma completedRankBetti_hasFiniteSupport
    (X : (supportedCompletedRankQuotient (s := s) z).FullSubcategory) :
    Function.HasFiniteSupport (completedRankBetti lam hfg z hJ hfin U hU hs X) :=
  completedSupportedBetti_hasFiniteSupport lam hfg z hJ hfin U hU hs _

lemma completedRankBetti_iso
    {X Y : (supportedCompletedRankQuotient (s := s) z).FullSubcategory} (i : X ≅ Y) (q : ℤ) :
    completedRankBetti lam hfg z hJ hfin U hU hs X q =
      completedRankBetti lam hfg z hJ hfin U hU hs Y q :=
  lengthQuotientValue_iso lam s U hU hs
    ((completedRankHomology lam hfg z hJ hfin U hU hs q).mapIso i)

/-- 商で零となった射の錐に対する一段の公式。 -/
lemma completedRankBetti_zero_cone
    (T : Triangle (supportedCompletedRankQuotient (s := s) z).FullSubcategory)
    (hT : T ∈ distTriang _) (hf : T.mor₁ = 0) (q : ℤ) :
    completedRankBetti lam hfg z hJ hfin U hU hs T.obj₃ q =
      completedRankBetti lam hfg z hJ hfin U hU hs T.obj₂ q +
        completedRankBetti lam hfg z hJ hfin U hU hs T.obj₁ (q + 1) := by
  let E := (supportedKaroubiEquivalence (s := s) z).inverse
  exact completedSupportedBetti_zero_cone lam hfg z hJ hfin U hU hs (E.mapTriangle.obj T)
    (E.map_distinguished T hT) (by change E.map T.mor₁ = 0; rw [hf, E.map_zero]) q

/-- 完備化の比較関手の像では、元の支持つき商のホモロジーの長さに一致する。 -/
lemma completedRankBetti_obj
    (X : SupportedSequenceRankQuotient (s := s) z) (q : ℤ) :
    completedRankBetti lam hfg z hJ hfin U hU hs
      ((supportedKaroubiFunctor z).obj ((toKaroubi _).obj X)) q =
      lengthQuotientValue lam s U hU hs
        ((supportedRankHomology lam hfg z hJ hfin U hU hs q).obj X) := by
  let E := supportedKaroubiEquivalence (s := s) z
  exact lengthQuotientValue_iso lam s U hU hs
    ((completedSupportedHomology lam hfg z hJ hfin U hU hs q).mapIso
      (E.unitIso.symm.app ((toKaroubi _).obj X)) ≪≫
        (completedSupportedHomologyFactors lam hfg z hJ hfin U hU hs q).app X)

end SerrePositivity.Asymptotic

end CompletedRankEvaluationPart

section CompletedKoszulFormulaPart

set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
open CategoryTheory.Pretriangulated Filter

variable {R : Type u} [CommRing R] [Nontrivial R] {s : ℕ → ℕ}

/-- 有界自由複体列からランク商の冪等完備化への標準関手。 -/
noncomputable abbrev completedSequenceFunctor :
    SequenceHomotopy R s ⥤ CompletedSequenceRankQuotient R s :=
  sequenceRankQuotientFunctor ⋙ toKaroubi _

variable {e : ℕ} (z : Fin e → R)

/-- 商の完備化で支持される複体列を支持部分圏の対象として見る。 -/
noncomputable abbrev completedComplexObj (K : CochainComplex (FreeSequence R s) ℤ)
    (hK : strictlyBoundedComplex _ K)
    (h : scalarSupported z (completedSequenceFunctor.obj (sequenceHomotopyObj K hK))) :
    (supportedCompletedRankQuotient (s := s) z).FullSubcategory :=
  ⟨completedSequenceFunctor.obj (sequenceHomotopyObj K hK), h⟩

variable {J : Ideal R} (lam : NormalizedLength R J) (hfg : J.FG)
  (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ i, lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology i) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

/-- 零となるスカラーに沿って反復した実際の Koszul 複体のホモロジー長。 -/
lemma completedRankBetti_sequenceKoszul_pow {n : ℕ} (x : Fin n → R)
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : scalarSupported z (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)))
    (hx : ∀ j, x j • 𝟙 (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)) = 0)
    (q : ℤ) :
    completedRankBetti lam hfg z hJ hfin U hU hs
      (completedComplexObj z (sequenceKoszul x K) (sequenceKoszul_bounded x K hK)
        (sequenceKoszul_map_supported completedSequenceFunctor z x K hK h)) q =
      ((cochainLengthShift + 1) ^ n)
        (completedRankBetti lam hfg z hJ hfin U hU hs (completedComplexObj z K hK h)) q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
      let P := sequenceKoszul (Fin.init x) K
      let hP := sequenceKoszul_bounded (Fin.init x) K hK
      let c := x (Fin.last n)
      let T := sequenceConeTriangle (c • 𝟙 P) hP hP
      let F := completedSequenceFunctor (R := R) (s := s)
      have hT := F.map_distinguished T (sequenceConeTriangle_distinguished _ _ _)
      have hp := sequenceKoszul_map_supported F z (Fin.init x) K hK h
      have hp' := sequenceKoszul_map_supported F z x K hK h
      let T' := fullSubcategoryTriangle (supportedCompletedRankQuotient z)
        (F.mapTriangle.obj T) hp hp hp'
      have hc := sequenceKoszul_map_smul_zero F (Fin.init x) K hK
        (fun j ↦ hx j.castSucc) c (hx (Fin.last n))
      have hf : T'.mor₁ = 0 := by
        apply ObjectProperty.hom_ext
        change F.map (show sequenceHomotopyObj P hP ⟶ sequenceHomotopyObj P hP from
          (sequenceConeTriangle (c • 𝟙 P) hP hP).mor₁) = 0
        rw [sequenceConeTriangle_smul_mor₁, F.map_smul, F.map_id]
        exact hc
      have he := completedRankBetti_zero_cone lam hfg z hJ hfin U hU hs T'
        (fullSubcategoryTriangle_distinguished _ _ _ _ _ hT) hf q
      change completedRankBetti lam hfg z hJ hfin U hU hs T'.obj₃ q = _
      rw [he]
      change completedRankBetti lam hfg z hJ hfin U hU hs
        (completedComplexObj z P hP hp) q +
          completedRankBetti lam hfg z hJ hfin U hU hs
            (completedComplexObj z P hP hp) (q + 1) = _
      rw [ih (Fin.init x) (fun j ↦ hx j.castSucc) q,
        ih (Fin.init x) (fun j ↦ hx j.castSucc) (q + 1)]
      rw [pow_succ', Module.End.mul_apply]
      simp only [LinearMap.add_apply, cochainLengthShift_apply, Module.End.one_apply,
        Pi.add_apply, add_comm]

/-- 公式 (4.2) の cochain 次数での二項係数部分。 -/
lemma completedRankBetti_sequenceKoszul {n : ℕ} (x : Fin n → R)
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : scalarSupported z (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)))
    (hx : ∀ j, x j • 𝟙 (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)) = 0)
    (q : ℤ) :
    completedRankBetti lam hfg z hJ hfin U hU hs
      (completedComplexObj z (sequenceKoszul x K) (sequenceKoszul_bounded x K hK)
        (sequenceKoszul_map_supported completedSequenceFunctor z x K hK h)) q =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
        completedRankBetti lam hfg z hJ hfin U hU hs (completedComplexObj z K hK h) (q + j) := by
  let y : ℕ → R := fun k ↦ if hk : k < n then x ⟨k, hk⟩ else 0
  have hy : (fun j : Fin n ↦ y j) = x := by funext j; simp [y, j.isLt]
  let X := sequenceKoszulTowerObj completedSequenceFunctor z y K hK h
  let T := sequenceKoszulTowerTriangle completedSequenceFunctor z y K hK h
  let H := completedRankHomology lam hfg z hJ hfin U hU hs 0
  have hT := sequenceKoszulTower_zero_triangles completedSequenceFunctor z y K hK h n
    (fun j hj ↦ by simpa [y, hj] using hx ⟨j, hj⟩)
  have he := iteratedZeroCone_length_binomial X (fun k ↦ (T k).mor₂)
    (fun k ↦ (T k).mor₃) n hT H (lengthQuotientValue lam s U hU hs)
    (lengthQuotientValue_add lam s U hU hs) q
  have hval (k : ℕ) (i : ℤ) :
      lengthQuotientValue lam s U hU hs ((H.shift i).obj (X k)) =
        completedRankBetti lam hfg z hJ hfin U hU hs (X k) i :=
    lengthQuotientValue_iso lam s U hU hs
      ((completedRankHomologyShiftNatIso lam hfg z hJ hfin U hU hs i).app (X k))
  rw [hval] at he
  have hleft : completedRankBetti lam hfg z hJ hfin U hU hs (X n) q =
      completedRankBetti lam hfg z hJ hfin U hU hs
        (completedComplexObj z (sequenceKoszul x K) (sequenceKoszul_bounded x K hK)
          (sequenceKoszul_map_supported completedSequenceFunctor z x K hK h)) q := by
    change completedRankBetti lam hfg z hJ hfin U hU hs
      (completedComplexObj z (sequenceKoszul (fun j : Fin n ↦ y j) K) _ _) q = _
    simp only [hy]
  rw [← hleft, he]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  exact hval 0 (q + j)

end SerrePositivity.Asymptotic

end CompletedKoszulFormulaPart

section CompletedComplexEvaluationPart

set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
open CategoryTheory.Pretriangulated Filter

variable {R : Type u} [CommRing R] [Nontrivial R] {s : ℕ → ℕ}
  {e : ℕ} (z : Fin e → R)

/-- 一様支持複体の直接の像と、支持つき商を経由した像の比較。 -/
noncomputable def completedComplexSupportedIso
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (hzK : supportedSequence z (sequenceHomotopyObj K hK))
    (h : scalarSupported z (completedSequenceFunctor.obj (sequenceHomotopyObj K hK))) :
    completedComplexObj z K hK h ≅
      (supportedKaroubiFunctor z).obj ((toKaroubi _).obj
        ((rankSmallBounded.inverseImage (supportedSequence z).ι).trW.Q.obj
          ⟨sequenceHomotopyObj K hK, hzK⟩)) := by
  let A := supportedSequence (s := s) z
  let B := rankSmallBounded (R := R) (s := s)
  let L := (B.inverseImage A.ι).trW.Q
  let Φ := A.triangulatedLocalizerMorphism B
  let F := supportedRankQuotientInclusion (s := s) z
  let X : A.FullSubcategory := ⟨sequenceHomotopyObj K hK, hzK⟩
  let i : sequenceRankQuotientFunctor.obj X.obj ≅ F.obj (L.obj X) :=
    (CatCommSq.iso Φ.functor L B.trW.Q (Φ.localizedFunctor L B.trW.Q)).app X
  exact ObjectProperty.isoMk _ ((toKaroubi _).mapIso i ≪≫
    (((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app F).app (L.obj X)).symm)

variable {J : Ideal R} (lam : NormalizedLength R J) (hfg : J.FG)
  (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ i, lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology i) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

/-- 一様支持複体列では、完備化後の値は各段のホモロジー長の正規化超極限。 -/
lemma completedRankBetti_complex
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (hzK : supportedSequence z (sequenceHomotopyObj K hK))
    (h : scalarSupported z (completedSequenceFunctor.obj (sequenceHomotopyObj K hK))) (q : ℤ) :
    completedRankBetti lam hfg z hJ hfin U hU hs (completedComplexObj z K hK h) q =
      normalizedLimit U s (fun n ↦ (lam.len (((evaluateComplex n).obj K).homology q)).toReal) := by
  rw [completedRankBetti_iso lam hfg z hJ hfin U hU hs
    (completedComplexSupportedIso z K hK hzK h) q,
    completedRankBetti_obj]
  exact supportedRankHomology_length_complex lam hfg z hJ hfin U hU hs K hK hzK q

/-- 公式 (4.2)：商でパラメータの冪が零なら、Koszul ホモロジー長の超極限が
元の非負な係数の二項畳み込みで計算される。元の複体列の一様支持は仮定しない。 -/
theorem completedRankBetti_koszul_formula
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : scalarSupported z (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)))
    (v : ℕ) (hv : 0 < v)
    (hx : ∀ j, z j ^ v • 𝟙 (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)) = 0)
    (i : ℤ) :
    normalizedLimit U s (fun n ↦ (lam.len
      ((koszulComplexOn (fun j ↦ z j ^ v) ((evaluateComplex n).obj K)).homology (-i))).toReal) =
      ∑ j ∈ Finset.range (e + 1), (e.choose j : ℝ) *
        completedRankBetti lam hfg z hJ hfin U hU hs
          (completedComplexObj z K hK h) (-(i - j)) := by
  let x := fun j ↦ z j ^ v
  let h' := sequenceKoszul_map_supported completedSequenceFunctor z x K hK h
  have he := completedRankBetti_sequenceKoszul z lam hfg hJ hfin U hU hs x K hK h hx (-i)
  rw [completedRankBetti_complex z lam hfg hJ hfin U hU hs _ _
    (sequenceKoszul_pow_supported z v hv K hK) h' (-i)] at he
  have hn : (fun n ↦
      (lam.len (((evaluateComplex n).obj (sequenceKoszul x K)).homology (-i))).toReal) =
      (fun n ↦ (lam.len
        ((koszulComplexOn x ((evaluateComplex n).obj K)).homology (-i))).toReal) := by
    funext n
    exact congrArg ENNReal.toReal (lam.len_congr _ _
      (((HomologicalComplex.homologyFunctor _ _ (-i)).mapIso
        (evaluateSequenceKoszulIso x K n)).toLinearEquiv))
  rw [hn] at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro j hj
  congr 2
  omega

end SerrePositivity.Asymptotic

end CompletedComplexEvaluationPart

section CompletedBaseChangeSupportPart

set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Functor CategoryTheory.Idempotents

variable {R S : Type u} [CommRing R] [Nontrivial R] [CommRing S] [Nontrivial S]
  {s : ℕ → ℕ} (φ : R →+* S)

omit [Nontrivial R] [Nontrivial S] in
lemma sequenceChangeRing_map_smul_id (X : SequenceHomotopy R s) (r : R) :
    (mapBoundedHomotopy (FreeSequence.changeRing φ)).map (r • 𝟙 X) =
      φ r • 𝟙 ((mapBoundedHomotopy (FreeSequence.changeRing φ)).obj X) := by
  obtain ⟨Y, hY⟩ := X
  obtain ⟨K, rfl⟩ := Y.quotient_obj_surjective
  apply ObjectProperty.hom_ext
  change ((FreeSequence.changeRing φ).mapHomotopyCategory (.up ℤ)).map
    (r • 𝟙 ((HomotopyCategory.quotient _ _).obj K)) = _
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul]
  change (HomotopyCategory.quotient _ _).map
    (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).map (r • 𝟙 K)) = _
  rw [changeRing_complex_map_smul, CategoryTheory.Functor.map_id,
    Functor.map_smul, CategoryTheory.Functor.map_id]
  rfl

lemma rankQuotientChangeRing_map_smul_id (X : SequenceRankQuotient R s) (r : R) :
    (rankQuotientChangeRing φ).map (r • 𝟙 X) =
      φ r • 𝟙 ((rankQuotientChangeRing φ).obj X) := by
  apply map_smul_id_of_precomp φ sequenceRankQuotientFunctor (rankQuotientChangeRing φ)
    _ (rankQuotientChangeRing_fac φ) _ X r
  intro Y a
  simp only [Functor.comp_obj, Functor.comp_map, sequenceChangeRing_map_smul_id, Functor.map_smul,
    CategoryTheory.Functor.map_id]

/-- 全体のランク商の完備化上の標準的な係数変更。 -/
noncomputable abbrev completedChangeRing :
    CompletedSequenceRankQuotient R s ⥤ CompletedSequenceRankQuotient S s :=
  (functorExtension₂ _ _).obj (rankQuotientChangeRing φ)

lemma completedChangeRing_map_smul_id (X : CompletedSequenceRankQuotient R s) (r : R) :
    (completedChangeRing φ).map (r • 𝟙 X) =
      φ r • 𝟙 ((completedChangeRing φ).obj X) := by
  have h : (rankQuotientChangeRing φ).map (r • X.p) =
      φ r • (rankQuotientChangeRing φ).map X.p := by
    calc
      _ = (rankQuotientChangeRing φ).map (X.p ≫ (r • 𝟙 X.X)) := by simp
      _ = _ := by rw [Functor.map_comp, rankQuotientChangeRing_map_smul_id]; simp
  exact Karoubi.hom_ext _ _ h

/-- 商の完備化で初めて現れる支持も係数変更で保たれる。 -/
lemma completedChangeRing_supported {e : ℕ} (z : Fin e → R)
    (X : CompletedSequenceRankQuotient R s) (hX : scalarSupported z X) :
    scalarSupported (φ ∘ z) ((completedChangeRing φ).obj X) := by
  obtain ⟨v, hv, h⟩ := hX
  refine ⟨v, hv, fun j ↦ ?_⟩
  have hj := (completedChangeRing φ).congr_map (h j)
  simpa only [Function.comp_apply, completedChangeRing_map_smul_id, map_pow,
    Functor.map_zero] using hj

/-- 共通有界複体列からの像と係数変更の可換性。 -/
noncomputable def completedChangeRingFactors :
    completedSequenceFunctor (R := R) (s := s) ⋙ completedChangeRing φ ≅
      mapBoundedHomotopy (FreeSequence.changeRing φ) ⋙ completedSequenceFunctor :=
  isoWhiskerLeft sequenceRankQuotientFunctor
    ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app (rankQuotientChangeRing φ)) ≪≫
    isoWhiskerRight (rankQuotientChangeRing_fac φ) (toKaroubi _)

end SerrePositivity.Asymptotic

end CompletedBaseChangeSupportPart

section PaperRankQuotientPart

set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Functor CategoryTheory.Idempotents
open CategoryTheory.Limits

variable (R : Type u) [CommRing R] [Nontrivial R] (s : ℕ → ℕ)

/-- 論文の D_S：共通有界な自由列のホモトピー圏の冪等完備化。 -/
abbrev PaperSequenceCategory := Karoubi (SequenceHomotopy R s)

/-- 論文の N_S：小さいランクの列の像から生成される厚い部分圏。 -/
abbrev paperRankNull : ObjectProperty (PaperSequenceCategory R s) :=
  karoubiNullEnvelope (rankSmallBounded (R := R) (s := s))

/-- 論文の P_S：完備化、厚い部分圏による商、再び完備化の順で構成する。 -/
abbrev PaperRankQuotient := Karoubi ((paperRankNull R s).trW.Localization)

noncomputable abbrev paperRankEquivalence :
    PaperRankQuotient R s ≌ CompletedSequenceRankQuotient R s :=
  karoubiVerdierOrderEquivalence (rankSmallBounded (R := R) (s := s))

noncomputable abbrev paperSequenceFunctor : SequenceHomotopy R s ⥤ PaperRankQuotient R s :=
  karoubiFirstFromOriginal (rankSmallBounded (R := R) (s := s))

/-- 実際の複体列からの標準関手との両立。 -/
noncomputable def paperSequenceComparison :
    paperSequenceFunctor R s ⋙ (paperRankEquivalence R s).functor ≅ completedSequenceFunctor :=
  isoWhiskerLeft (toKaroubi _ ⋙ (paperRankNull R s).trW.Q)
    (completedKaroubiFirstToLastFactors _) ≪≫
  isoWhiskerLeft (toKaroubi _) (karoubiFirstToLastFactors _) ≪≫
    (functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app sequenceRankQuotientFunctor

variable {R s} {e : ℕ} (z : Fin e → R)

/-- 論文の P_S^J に対応する支持部分圏。 -/
abbrev paperSupportedRank : ObjectProperty (PaperRankQuotient R s) := scalarSupported z

/-- 論文の支持部分圏と構成済みの評価の定義域との線形三角同値。 -/
noncomputable abbrev paperSupportedRankEquivalence :
    (paperSupportedRank (s := s) z).FullSubcategory ≌
      (supportedCompletedRankQuotient (s := s) z).FullSubcategory :=
  scalarSupportEquivalence (paperRankEquivalence R s) z

/-- 支持つき商の完備化との比較も合成で得られる。 -/
noncomputable def paperSupportedToKaroubi :
    (paperSupportedRank (s := s) z).FullSubcategory ≌
      Karoubi (SupportedSequenceRankQuotient (s := s) z) :=
  (paperSupportedRankEquivalence z).trans (supportedKaroubiEquivalence z).symm

noncomputable instance paperSupportedToKaroubi_functor_commShift :
    (paperSupportedToKaroubi (s := s) z).functor.CommShift ℤ :=
  inferInstanceAs (((paperSupportedRankEquivalence z).functor ⋙
    (supportedKaroubiEquivalence z).inverse).CommShift ℤ)

noncomputable instance paperSupportedToKaroubi_inverse_commShift :
    (paperSupportedToKaroubi (s := s) z).inverse.CommShift ℤ :=
  inferInstanceAs (((supportedKaroubiEquivalence z).functor ⋙
    (paperSupportedRankEquivalence z).inverse).CommShift ℤ)

instance paperSupportedToKaroubi_functor_isTriangulated :
    (paperSupportedToKaroubi (s := s) z).functor.IsTriangulated :=
  inferInstanceAs (((paperSupportedRankEquivalence z).functor ⋙
    (supportedKaroubiEquivalence z).inverse).IsTriangulated)

instance paperSupportedToKaroubi_inverse_isTriangulated :
    (paperSupportedToKaroubi (s := s) z).inverse.IsTriangulated :=
  inferInstanceAs (((supportedKaroubiEquivalence z).functor ⋙
    (paperSupportedRankEquivalence z).inverse).IsTriangulated)

end SerrePositivity.Asymptotic

end PaperRankQuotientPart

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite Paper "Lemma 4.2"] _root_.SerrePositivity.Asymptotic.paperSupportedToKaroubi
attribute [cite Paper "Lemma 4.2"] _root_.SerrePositivity.Asymptotic.paperSupportedToKaroubi_functor_isTriangulated
