module

public import SerrePositivity.Asymptotic.SequenceKoszul
public import SerrePositivity.Asymptotic.RankQuotient
public import SerrePositivity.Asymptotic.LengthSequence
public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
public import SerrePositivity.CategoryTheory.Triangulated.VerdierLift
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import SerrePositivity.Asymptotic.Karoubi
public import SerrePositivity.CategoryTheory.Karoubi.Basic
public import SerrePositivity.CategoryTheory.Karoubi.Triangulated

/-! # 台を持つ自由列のホモロジーと長さの商

## 概要

共通の零ホモトピーを持つ自由複体の列のホモロジー列が長さで制限したアーベル圏に入ることを示し、ホモロジー関手を作ってランク商へ降ろす（小さいランクの対象は長さの商で零）。シフトとの比較とその自然性、冪等完備化した商への延長と、非零次数が有限範囲に入ることを与える。

## 方針

各段のホモロジーを離散関手として組み、台の共通指数の冪の Koszul 複体で評価する。冪等完備化への延長は値域のアーベル圏の冪等完備性の普遍性による。

## 規約

要求する Koszul ホモロジーの有限性は明示的な入力。

## 使われ方

`Euler`・`Completed`・`UniformLift`。
-/

@[expose] public noncomputable section

universe u

section SequenceHomologyBoundsPart

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits Filter Asymptotics

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}

/-- 自由列の複体の第 `q` ホモロジーを段ごとに並べた加群列。 -/
noncomputable def complexHomologySequence (P : CochainComplex (FreeSequence R s) ℤ)
    (q : ℤ) : ModuleSequence R :=
  Discrete.functor (fun n : ℕ ↦ ((evaluateComplex n).obj P).homology q)

variable {J : Ideal R} (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (x : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range x)).radical)

include hfg hJ in
/-- 共通の零ホモトピーから、ホモロジー列を一様に消すイデアル冪を得る。 -/
lemma complexHomologySequence_uniformlyPowTorsion
    (P : CochainComplex (FreeSequence R s) ℤ)
    (hnull : ∀ n j, Nonempty (Homotopy (smulId (x j) ((evaluateComplex n).obj P)) 0))
    (q : ℤ) : uniformlyPowTorsion J (complexHomologySequence P q) := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hJ hfg
  refine ⟨k, fun n ↦ hk.trans ?_⟩
  apply Ideal.span_le.mpr
  rintro _ ⟨j, rfl⟩
  obtain ⟨H⟩ := hnull n j
  have h := H.homologyMap_eq q
  change HomologicalComplex.homologyMap (x j • 𝟙 _) q =
    HomologicalComplex.homologyMap 0 q at h
  rw [homologyMap_smul, HomologicalComplex.homologyMap_id,
    HomologicalComplex.homologyMap_zero] at h
  change x j ∈ Module.annihilator R (((evaluateComplex n).obj P).homology q)
  rw [Module.mem_annihilator]
  intro m
  exact congrArg (fun f ↦ f.hom m) h

variable (hfin : ∀ i, lam.len ((koszulComplex x).homology i) ≠ ⊤)

include hfg hJ hfin in
/-- 零ホモトピーによる Koszul 直和因子表示から各段の有限性を得る。 -/
lemma complexHomologySequence_ne_top (P : CochainComplex (FreeSequence R s) ℤ)
    (hP : strictlyBoundedComplex (FreeSequence R s) P)
    (hnull : ∀ n j, Nonempty (Homotopy (smulId (x j) ((evaluateComplex n).obj P)) 0))
    (n : ℕ) (q : ℤ) : lam.len ((complexHomologySequence P q).obj ⟨n⟩) ≠ ⊤ := by
  obtain ⟨a, w, hbound⟩ := sequenceComplex_uniform_interval P hP
  exact ne_top_of_le_ne_top (ennreal_sum_nsmul_ne_top (Finset.range w)
    (fun j ↦ lam.len ((koszulComplex x).homology (q - (a + j)))) (fun _ _ ↦ hfin _)
    (fun j ↦ (P.X (a + j)).rank n))
    (lambdaHomology_le_sum_of_nullHomotopies lam hfg x hJ a w
      (fun i ↦ (P.X i).rank n) ((evaluateComplex n).obj P) (hbound n)
      (fun _ _ _ ↦ ⟨Iso.refl _⟩) (hnull n) q)

include hfg hJ hfin in
/-- 台の一様な自由複体列のホモロジーは長さで制限したアーベル圏に入る。 -/
lemma complexHomologySequence_lengthBounded (P : CochainComplex (FreeSequence R s) ℤ)
    (hP : strictlyBoundedComplex (FreeSequence R s) P)
    (hnull : ∀ n j, Nonempty (Homotopy (smulId (x j) ((evaluateComplex n).obj P)) 0))
    (q : ℤ) : lengthBoundedSequence lam s (complexHomologySequence P q) := by
  refine ⟨complexHomologySequence_uniformlyPowTorsion hfg x hJ P hnull q,
    fun n ↦ complexHomologySequence_ne_top lam hfg x hJ hfin P hP hnull n q, ?_⟩
  obtain ⟨a, w, hbound⟩ := sequenceComplex_uniform_interval P hP
  exact lambdaHomology_isBigO_of_nullHomotopies lam hfg x hJ hfin a w
    (fun n i ↦ (P.X i).rank n) (fun n ↦ (evaluateComplex n).obj P) hbound
    (fun _ _ _ _ ↦ ⟨Iso.refl _⟩) hnull _ (fun i _ _ ↦ (P.X i).rank_isBigO) q

include hfg hJ hfin in
/-- ランクの小さい支持つき列のホモロジーの長さは `o(s)` である。 -/
lemma complexHomologySequence_isLittleO (P : CochainComplex (FreeSequence R s) ℤ)
    (hP : rankSmallComplex P)
    (hnull : ∀ n j, Nonempty (Homotopy (smulId (x j) ((evaluateComplex n).obj P)) 0))
    (q : ℤ) : (fun n ↦ (lam.len ((complexHomologySequence P q).obj ⟨n⟩)).toReal)
      =o[atTop] (fun n ↦ (s n : ℝ)) := by
  obtain ⟨a, w, hbound⟩ := sequenceComplex_uniform_interval P hP.1
  exact lambdaHomology_isLittleO_of_nullHomotopies lam hfg x hJ hfin a w
    (fun n i ↦ (P.X i).rank n) (fun n ↦ (evaluateComplex n).obj P) hbound
    (fun _ _ _ _ ↦ ⟨Iso.refl _⟩) hnull _ (fun i _ _ ↦ hP.2 i) q

/-- 有界支持つき列のホモロジーを長さで制限した圏の対象とみなす。 -/
noncomputable def boundedComplexHomologySequence (P : CochainComplex (FreeSequence R s) ℤ)
    (hP : strictlyBoundedComplex (FreeSequence R s) P)
    (hnull : ∀ n j, Nonempty (Homotopy (smulId (x j) ((evaluateComplex n).obj P)) 0))
    (q : ℤ) : LengthBoundedSequence lam s :=
  ⟨complexHomologySequence P q,
    complexHomologySequence_lengthBounded lam hfg x hJ hfin P hP hnull q⟩

/-- ランクの小さい支持つき列のホモロジーは、長さの Serre 商で零となる。 -/
lemma boundedComplexHomologySequence_isZero
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)
    (P : CochainComplex (FreeSequence R s) ℤ) (hP : rankSmallComplex P)
    (hnull : ∀ n j, Nonempty (Homotopy (smulId (x j) ((evaluateComplex n).obj P)) 0))
    (q : ℤ) : IsZero ((lengthSerreQuotientFunctor lam s U hU hs).obj
      (boundedComplexHomologySequence lam hfg x hJ hfin P hP.1 hnull q)) := by
  rw [lengthSerreQuotient_isZero_iff]
  exact normalizedLimit_eq_zero_of_isLittleO U hU s _
    (complexHomologySequence_isLittleO lam hfg x hJ hfin P hP hnull q)

end SerrePositivity.Asymptotic

end SequenceHomologyBoundsPart

section SequenceHomologyPart

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits Filter

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}

/-- 共通有界ホモトピー圏の第 `n` 段の第 `q` ホモロジーへの関手。 -/
noncomputable abbrev sequenceHomologyEvaluation (q : ℤ) (n : ℕ) :
    SequenceHomotopy R s ⥤ ModuleCat.{u} R :=
  boundedHomotopyInclusion _ ⋙ (FreeSequence.evaluation n).mapHomotopyCategory (.up ℤ) ⋙
    HomotopyCategory.homologyFunctor _ _ q

/-- 共通有界自由列のホモロジーを加群列にまとめた関手。 -/
noncomputable def sequenceHomology (q : ℤ) : SequenceHomotopy R s ⥤ ModuleSequence R where
  obj P := Discrete.functor (fun n : ℕ ↦ (sequenceHomologyEvaluation q n).obj P)
  map f := Discrete.natTrans (fun n ↦ (sequenceHomologyEvaluation q n.as).map f)
  map_id P := by
    apply NatTrans.ext
    funext n
    exact CategoryTheory.Functor.map_id (sequenceHomologyEvaluation q n.as) P
  map_comp f g := by
    apply NatTrans.ext
    funext n
    exact CategoryTheory.Functor.map_comp (sequenceHomologyEvaluation q n.as) f g

instance sequenceHomology_additive (q : ℤ) : (sequenceHomology (R := R) (s := s) q).Additive where
  map_add {X Y} f g := by
    apply NatTrans.ext
    funext n
    exact Functor.map_add (sequenceHomologyEvaluation q n.as)

/-- 代表複体で計算したホモロジー列との比較同型。 -/
noncomputable def sequenceHomologyComplexIso (P : CochainComplex (FreeSequence R s) ℤ)
    (hP : strictlyBoundedComplex (FreeSequence R s) P) (q : ℤ) :
    (sequenceHomology q).obj (sequenceHomotopyObj P hP) ≅ complexHomologySequence P q :=
  Discrete.natIso (fun n ↦
    (HomotopyCategory.homologyFunctor _ _ q).mapIso
      (((FreeSequence.evaluation n.as).mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
    (HomotopyCategory.homologyFunctorFactors _ _ q).app ((evaluateComplex n.as).obj P))

variable {J : Ideal R} (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (z : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ i, lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology i) ≠ ⊤)

include hfg hJ hfin in
/-- 一様な台をもつ自由列のホモロジーは長さで制限した圏に属する。 -/
lemma sequenceHomology_lengthBounded (P : SequenceHomotopy R s)
    (hP : supportedSequence z P) (q : ℤ) :
    lengthBoundedSequence lam s ((sequenceHomology q).obj P) := by
  obtain ⟨Y, hY⟩ := P
  obtain ⟨K, rfl⟩ := Y.quotient_obj_surjective
  have hb := (boundedHomotopyProperty_quotient _ K).mp hY
  obtain ⟨v, hv, hn⟩ := (sequence_supported_iff z K hb).mp hP
  apply (lengthBoundedSequence lam s).prop_of_iso (sequenceHomologyComplexIso K hb q).symm
  exact complexHomologySequence_lengthBounded lam hfg (fun j ↦ z j ^ v)
    (le_radical_span_pow z hJ v) (hfin v hv) K hb (fun n j ↦ hn j n) q

/-- 支持つき自由列から長さで制限した加群列へのホモロジー関手。 -/
noncomputable def supportedSequenceHomology (q : ℤ) :
    (supportedSequence (s := s) z).FullSubcategory ⥤ LengthBoundedSequence lam s :=
  (lengthBoundedSequence lam s).lift ((supportedSequence z).ι ⋙ sequenceHomology q)
    (fun P ↦ sequenceHomology_lengthBounded lam hfg z hJ hfin P.obj P.property q)

instance supportedSequenceHomology_additive (q : ℤ) :
    (supportedSequenceHomology (s := s) lam hfg z hJ hfin q).Additive := by
  dsimp only [supportedSequenceHomology]
  infer_instance

/-- 支持つき自由列のホモロジーを長さの Serre 商に送る関手。 -/
noncomputable def supportedSequenceQuotientHomology
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n) (q : ℤ) :
    (supportedSequence (s := s) z).FullSubcategory ⥤ LengthSerreQuotient lam s U hU hs :=
  supportedSequenceHomology lam hfg z hJ hfin q ⋙ lengthSerreQuotientFunctor lam s U hU hs

end SerrePositivity.Asymptotic

end SequenceHomologyPart

section SequenceHomologyLocalizationPart

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Filter

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}

/-- 加群列の完全性は各段の完全性から従う。 -/
lemma moduleSequence_exact_of_eval (S : ShortComplex (ModuleSequence R))
    (hS : ∀ n, (S.map (moduleSequenceEvaluation n)).Exact) : S.Exact := by
  rw [S.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
  apply NatTrans.ext
  funext n
  have hn : IsZero ((moduleSequenceEvaluation n.as).obj S.homology) :=
    ((S.map (moduleSequenceEvaluation n.as)).exact_iff_isZero_homology.mp (hS n.as)).of_iso
      (S.mapHomologyIso (moduleSequenceEvaluation n.as)).symm
  exact hn.eq_of_src _ _

instance sequenceHomology_isHomological (q : ℤ) :
    (sequenceHomology (R := R) (s := s) q).IsHomological where
  exact T hT := by
    apply moduleSequence_exact_of_eval
    intro n
    exact (sequenceHomologyEvaluation q n).map_distinguished_exact T hT

variable {J : Ideal R} (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (z : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ i, lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology i) ≠ ⊤)

instance supportedSequenceHomology_isHomological (q : ℤ) :
    (supportedSequenceHomology (s := s) lam hfg z hJ hfin q).IsHomological where
  exact T hT := by
    apply (ShortComplex.exact_map_iff_of_faithful _ (lengthBoundedSequence lam s).ι).mp
    exact ((supportedSequence (s := s) z).ι ⋙ sequenceHomology q).map_distinguished_exact T hT

variable (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

instance supportedSequenceQuotientHomology_additive (q : ℤ) :
    (supportedSequenceQuotientHomology lam hfg z hJ hfin U hU hs q).Additive := by
  dsimp only [supportedSequenceQuotientHomology]
  infer_instance

instance supportedSequenceQuotientHomology_isHomological (q : ℤ) :
    (supportedSequenceQuotientHomology lam hfg z hJ hfin U hU hs q).IsHomological where
  exact T hT :=
    ((supportedSequenceHomology lam hfg z hJ hfin q).map_distinguished_exact T hT).map
      (lengthSerreQuotientFunctor lam s U hU hs)

/-- 支持つき複体の小さいランク条件は、ホモロジー評価の消滅を与える。 -/
lemma supportedSequenceQuotientHomology_smallComplex
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : rankSmallComplex K)
    (hzK : supportedSequence z (sequenceHomotopyObj K hK.1)) (q : ℤ) :
    IsZero ((supportedSequenceQuotientHomology lam hfg z hJ hfin U hU hs q).obj
      ⟨sequenceHomotopyObj K hK.1, hzK⟩) := by
  obtain ⟨v, hv, hn⟩ := (sequence_supported_iff z K hK.1).mp hzK
  let Z := boundedComplexHomologySequence lam hfg (fun j ↦ z j ^ v)
    (le_radical_span_pow z hJ v) (hfin v hv) K hK.1 (fun n j ↦ hn j n) q
  let eZ : (supportedSequenceHomology lam hfg z hJ hfin q).obj
      ⟨sequenceHomotopyObj K hK.1, hzK⟩ ≅ Z :=
    ObjectProperty.isoMk _ (sequenceHomologyComplexIso K hK.1 q)
  exact (boundedComplexHomologySequence_isZero lam hfg (fun j ↦ z j ^ v)
    (le_radical_span_pow z hJ v) (hfin v hv) U hU hs K hK (fun n j ↦ hn j n) q).of_iso
    ((lengthSerreQuotientFunctor lam s U hU hs).mapIso eZ)

/-- ホモトピー同型で小さいランクの代表をもつ対象も零に送られる。 -/
lemma supportedSequenceQuotientHomology_small
    (P : (supportedSequence (s := s) z).FullSubcategory) (hP : rankSmallBounded P.obj) (q : ℤ) :
    IsZero ((supportedSequenceQuotientHomology lam hfg z hJ hfin U hU hs q).obj P) := by
  obtain ⟨Y, hY, ⟨iY⟩⟩ := hP
  obtain ⟨K, rfl⟩ := Y.quotient_obj_surjective
  have hK := (rankSmallHomotopy_quotient K).mp hY
  let iK : sequenceHomotopyObj K hK.1 ≅ P.obj := ObjectProperty.isoMk _ iY.symm
  have hzK := (supportedSequence z).prop_of_iso iK.symm P.property
  let iP : (⟨sequenceHomotopyObj K hK.1, hzK⟩ : (supportedSequence z).FullSubcategory) ≅ P :=
    ObjectProperty.isoMk _ iK
  exact (supportedSequenceQuotientHomology_smallComplex lam hfg z hJ hfin U hU hs K hK hzK q).of_iso
    ((supportedSequenceQuotientHomology lam hfg z hJ hfin U hU hs q).mapIso iP.symm)

variable [Nontrivial R]

/-- 長さの商へのホモロジー評価は支持つきランク商の分母を同型に送る。 -/
lemma supportedSequenceQuotientHomology_inverts (q : ℤ) :
    (rankSmallBounded.inverseImage (supportedSequence (s := s) z).ι).trW.IsInvertedBy
      (supportedSequenceQuotientHomology lam hfg z hJ hfin U hU hs q) :=
  homological_inverts_of_kills _ _
    (fun P hP ↦ supportedSequenceQuotientHomology_small lam hfg z hJ hfin U hU hs P hP q)

/-- 支持つき Verdier 商から長さの Serre 商へのホモロジー関手。 -/
noncomputable def supportedRankHomology (q : ℤ) :
    SupportedSequenceRankQuotient (s := s) z ⥤ LengthSerreQuotient lam s U hU hs :=
  Localization.lift (supportedSequenceQuotientHomology lam hfg z hJ hfin U hU hs q)
    (supportedSequenceQuotientHomology_inverts lam hfg z hJ hfin U hU hs q)
    (rankSmallBounded.inverseImage (supportedSequence z).ι).trW.Q

/-- 商上のホモロジー関手は、元の支持つき列上の評価と自然同型で一致する。 -/
noncomputable def supportedRankHomologyFactors (q : ℤ) :
    (rankSmallBounded.inverseImage (supportedSequence z).ι).trW.Q ⋙
      supportedRankHomology lam hfg z hJ hfin U hU hs q ≅
        supportedSequenceQuotientHomology lam hfg z hJ hfin U hU hs q :=
  Localization.fac _ (supportedSequenceQuotientHomology_inverts lam hfg z hJ hfin U hU hs q) _

/-- 降下したホモロジー評価も完全三角形を完全列に送る。 -/
instance supportedRankHomology_isHomological (q : ℤ) :
    (supportedRankHomology lam hfg z hJ hfin U hU hs q).IsHomological := by
  let B := rankSmallBounded.inverseImage (supportedSequence (s := s) z).ι
  let := Localization.essSurj_mapArrow B.trW.Q B.trW
  exact Functor.isHomological_of_localization B.trW.Q _ _
    (supportedRankHomologyFactors lam hfg z hJ hfin U hU hs q)

set_option synthInstance.maxSize 512 in
/-- 商上のホモロジー関手は加法的である。 -/
instance supportedRankHomology_additive (q : ℤ) :
    (supportedRankHomology lam hfg z hJ hfin U hU hs q).Additive := inferInstance

end SerrePositivity.Asymptotic

end SequenceHomologyLocalizationPart

section RankHomologyShiftPart

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits Filter

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}

/-- 自由列のホモロジー評価とシフトの比較。 -/
noncomputable def sequenceHomologyShiftIso (P : SequenceHomotopy R s) (q : ℤ) :
    (sequenceHomology 0).obj (P⟦q⟧) ≅ (sequenceHomology q).obj P :=
  Discrete.natIso (fun n ↦ by
    let G := boundedHomotopyInclusion (FreeSequence R s) ⋙
      (FreeSequence.evaluation n.as).mapHomotopyCategory (.up ℤ)
    let H := HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0
    exact H.mapIso ((G.commShiftIso q).app P) ≪≫ (H.isoShift q).app (G.obj P))

variable {J : Ideal R} (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (z : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ i, lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology i) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

/-- 長さの商に値をもつ支持つき列のホモロジーとシフトの比較。 -/
noncomputable def supportedSequenceQuotientHomologyShiftIso
    (P : (supportedSequence (s := s) z).FullSubcategory) (q : ℤ) :
    (supportedSequenceQuotientHomology lam hfg z hJ hfin U hU hs 0).obj (P⟦q⟧) ≅
      (supportedSequenceQuotientHomology lam hfg z hJ hfin U hU hs q).obj P :=
  (lengthSerreQuotientFunctor lam s U hU hs).mapIso (ObjectProperty.isoMk _
    ((sequenceHomology 0).mapIso (((supportedSequence z).ι.commShiftIso q).app P) ≪≫
      sequenceHomologyShiftIso P.obj q))

variable [Nontrivial R]

/-- 支持つきランク商上のホモロジーとシフトの比較。 -/
noncomputable def supportedRankHomologyShiftIso
    (P : SupportedSequenceRankQuotient (s := s) z) (q : ℤ) :
    (supportedRankHomology lam hfg z hJ hfin U hU hs 0).obj (P⟦q⟧) ≅
      (supportedRankHomology lam hfg z hJ hfin U hU hs q).obj P := by
  let L := (rankSmallBounded.inverseImage (supportedSequence (s := s) z).ι).trW.Q
  let := Localization.essSurj L (rankSmallBounded.inverseImage (supportedSequence z).ι).trW
  let X := L.objPreimage P
  let i := L.objObjPreimageIso P
  let H₀ := supportedRankHomology lam hfg z hJ hfin U hU hs 0
  let Hq := supportedRankHomology lam hfg z hJ hfin U hU hs q
  exact H₀.mapIso ((shiftFunctor _ q).mapIso i).symm ≪≫
    H₀.mapIso ((L.commShiftIso q).app X).symm ≪≫
    (supportedRankHomologyFactors lam hfg z hJ hfin U hU hs 0).app (X⟦q⟧) ≪≫
    supportedSequenceQuotientHomologyShiftIso lam hfg z hJ hfin U hU hs X q ≪≫
    ((supportedRankHomologyFactors lam hfg z hJ hfin U hU hs q).app X).symm ≪≫ Hq.mapIso i

end SerrePositivity.Asymptotic

end RankHomologyShiftPart

section CompletedHomologyPart

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents Filter

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}

/-- 共通有界な自由列のホモロジー列は共通の有限範囲の外で零となる。 -/
lemma sequenceHomology_bounded (P : SequenceHomotopy R s) :
    ∃ a b : ℤ, ∀ q, (q < a ∨ b < q) → IsZero ((sequenceHomology q).obj P) := by
  obtain ⟨Y, hY⟩ := P
  obtain ⟨K, rfl⟩ := Y.quotient_obj_surjective
  have hb := (boundedHomotopyProperty_quotient _ K).mp hY
  obtain ⟨a, b, ha, hb'⟩ := hb
  have hb : strictlyBoundedComplex (FreeSequence R s) K := ⟨a, b, ha, hb'⟩
  refine ⟨a, b, fun q hq ↦ ?_⟩
  have hz : IsZero (complexHomologySequence K q) := by
    apply Functor.isZero
    intro n
    apply isZero_homology_of_isZero_X
    apply (FreeSequence.evaluation n.as).map_isZero
    rcases hq with hq | hq
    · exact CochainComplex.isZero_of_isStrictlyGE K a q hq
    · exact CochainComplex.isZero_of_isStrictlyLE K b q hq
  exact hz.of_iso (sequenceHomologyComplexIso K hb q)

variable {J : Ideal R} (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (z : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ i, lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology i) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

/-- 長さの商に移した後も、ホモロジーの消滅範囲は維持される。 -/
lemma supportedSequenceQuotientHomology_bounded
    (P : (supportedSequence (s := s) z).FullSubcategory) :
    ∃ a b : ℤ, ∀ q, (q < a ∨ b < q) →
      IsZero ((supportedSequenceQuotientHomology lam hfg z hJ hfin U hU hs q).obj P) := by
  obtain ⟨a, b, hab⟩ := sequenceHomology_bounded P.obj
  refine ⟨a, b, fun q hq ↦ ?_⟩
  apply (lengthSerreQuotientFunctor lam s U hU hs).map_isZero
  rw [IsZero.iff_id_eq_zero]
  apply ObjectProperty.hom_ext
  exact (hab q hq).eq_of_src _ _

variable [Nontrivial R]

/-- Verdier 商の全対象について、ホモロジーの非零次数は有限範囲に入る。 -/
lemma supportedRankHomology_bounded (P : SupportedSequenceRankQuotient (s := s) z) :
    ∃ a b : ℤ, ∀ q, (q < a ∨ b < q) →
      IsZero ((supportedRankHomology lam hfg z hJ hfin U hU hs q).obj P) := by
  let L := (rankSmallBounded.inverseImage (supportedSequence (s := s) z).ι).trW.Q
  let := Localization.essSurj L (rankSmallBounded.inverseImage (supportedSequence z).ι).trW
  let X := L.objPreimage P
  obtain ⟨a, b, hab⟩ := supportedSequenceQuotientHomology_bounded lam hfg z hJ hfin U hU hs X
  refine ⟨a, b, fun q hq ↦ ?_⟩
  exact (hab q hq).of_iso
    ((supportedRankHomology lam hfg z hJ hfin U hU hs q).mapIso (L.objObjPreimageIso P).symm ≪≫
      (supportedRankHomologyFactors lam hfg z hJ hfin U hU hs q).app X)

/-- 支持つきランク商の Karoubi 包絡へのホモロジー関手の延長。 -/
noncomputable def completedSupportedHomology (q : ℤ) :
    Karoubi (SupportedSequenceRankQuotient (s := s) z) ⥤ LengthSerreQuotient lam s U hU hs :=
  (functorExtension _ _).obj (supportedRankHomology lam hfg z hJ hfin U hU hs q)

instance completedSupportedHomology_additive (q : ℤ) :
    (completedSupportedHomology lam hfg z hJ hfin U hU hs q).Additive := by
  dsimp only [completedSupportedHomology]
  infer_instance

/-- 冪等完備化前の対象では、延長したホモロジーは元のホモロジーと一致する。 -/
noncomputable def completedSupportedHomologyFactors (q : ℤ) :
    toKaroubi _ ⋙ completedSupportedHomology lam hfg z hJ hfin U hU hs q ≅
      supportedRankHomology lam hfg z hJ hfin U hU hs q :=
  karoubiExtensionToCompleteFactors _

/-- 形式的直和因子のホモロジーは、射影が誘導する冪等元の像に同型である。 -/
noncomputable def completedSupportedHomologyImageIso
    (P : Karoubi (SupportedSequenceRankQuotient (s := s) z)) (q : ℤ) :
    (completedSupportedHomology lam hfg z hJ hfin U hU hs q).obj P ≅
      Abelian.image ((supportedRankHomology lam hfg z hJ hfin U hU hs q).map P.p) :=
  karoubiExtensionImageIso _ P

/-- 形式的な直和因子でもホモロジーの非零次数は有限範囲に入る。 -/
lemma completedSupportedHomology_bounded
    (P : Karoubi (SupportedSequenceRankQuotient (s := s) z)) :
    ∃ a b : ℤ, ∀ q, (q < a ∨ b < q) →
      IsZero ((completedSupportedHomology lam hfg z hJ hfin U hU hs q).obj P) := by
  obtain ⟨a, b, hab⟩ := supportedRankHomology_bounded lam hfg z hJ hfin U hU hs P.X
  refine ⟨a, b, fun q hq ↦ ?_⟩
  let F := completedSupportedHomology lam hfg z hJ hfin U hU hs q
  let r := (karoubiRetract P).map F
  have hz := (hab q hq).of_iso
    ((completedSupportedHomologyFactors lam hfg z hJ hfin U hU hs q).app P.X)
  rw [IsZero.iff_id_eq_zero, ← r.retract, hz.eq_zero_of_src r.r, comp_zero]

/-- 全体の商の冪等完備化で台をもつ任意の対象を評価するホモロジー関手。 -/
noncomputable def completedRankHomology (q : ℤ) :
    (supportedCompletedRankQuotient (s := s) z).FullSubcategory ⥤
      LengthSerreQuotient lam s U hU hs :=
  (supportedKaroubiEquivalence z).inverse ⋙ completedSupportedHomology lam hfg z hJ hfin U hU hs q

/-- 全支持対象のホモロジーも対象ごとに共通の有限範囲をもつ。 -/
lemma completedRankHomology_bounded
    (P : (supportedCompletedRankQuotient (s := s) z).FullSubcategory) :
    ∃ a b : ℤ, ∀ q, (q < a ∨ b < q) →
      IsZero ((completedRankHomology lam hfg z hJ hfin U hU hs q).obj P) :=
  completedSupportedHomology_bounded lam hfg z hJ hfin U hU hs
    ((supportedKaroubiEquivalence z).inverse.obj P)

end SerrePositivity.Asymptotic

end CompletedHomologyPart

section RankHomologyShiftNaturalPart

set_option synthInstance.maxSize 512

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents Filter
open CategoryTheory.Functor

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}

/-- 自由列のホモロジーとシフトの比較は対象に自然。 -/
noncomputable def sequenceHomologyShiftNatIso (q : ℤ) :
    shiftFunctor (SequenceHomotopy R s) q ⋙ sequenceHomology 0 ≅ sequenceHomology q :=
  NatIso.ofComponents (fun P ↦ sequenceHomologyShiftIso P q) (fun {X Y} f ↦ by
    apply NatTrans.ext
    funext n
    let G := boundedHomotopyInclusion (FreeSequence R s) ⋙
      (FreeSequence.evaluation n.as).mapHomotopyCategory (.up ℤ)
    let H := HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0
    let e := isoWhiskerRight (G.commShiftIso q) H ≪≫ isoWhiskerLeft G (H.isoShift q)
    exact e.hom.naturality f)

variable {J : Ideal R} (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (z : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ i, lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology i) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

/-- 長さで制限したホモロジー関手のシフト比較。 -/
noncomputable def supportedSequenceHomologyShiftNatIso (q : ℤ) :
    shiftFunctor _ q ⋙ supportedSequenceHomology (s := s) lam hfg z hJ hfin 0 ≅
      supportedSequenceHomology lam hfg z hJ hfin q := by
  let i := (supportedSequence (s := s) z).ι
  let e := isoWhiskerRight (i.commShiftIso q) (sequenceHomology 0) ≪≫
    isoWhiskerLeft i (sequenceHomologyShiftNatIso q)
  exact NatIso.ofComponents (fun P ↦ ObjectProperty.isoMk _ (e.app P)) (fun f ↦ by
    apply ObjectProperty.hom_ext
    exact e.hom.naturality f)

/-- 長さの Serre 商に値をもつホモロジー関手のシフト比較。 -/
noncomputable def supportedSequenceQuotientHomologyShiftNatIso (q : ℤ) :
    shiftFunctor _ q ⋙ supportedSequenceQuotientHomology lam hfg z hJ hfin U hU hs 0 ≅
      supportedSequenceQuotientHomology lam hfg z hJ hfin U hU hs q :=
  isoWhiskerRight (supportedSequenceHomologyShiftNatIso lam hfg z hJ hfin q)
    (lengthSerreQuotientFunctor lam s U hU hs)

variable [Nontrivial R]

/-- 商上のシフト比較を局所化の完全忠実な前合成から降ろす。 -/
noncomputable def supportedRankHomologyShiftNatIso (q : ℤ) :
    shiftFunctor _ q ⋙ supportedRankHomology lam hfg z hJ hfin U hU hs 0 ≅
      supportedRankHomology lam hfg z hJ hfin U hU hs q := by
  let W := (rankSmallBounded.inverseImage (supportedSequence (s := s) z).ι).trW
  let L := W.Q
  let F := supportedRankHomology lam hfg z hJ hfin U hU hs 0
  let eq := isoWhiskerRight (L.commShiftIso q).symm F ≪≫
    isoWhiskerLeft (shiftFunctor _ q)
      (supportedRankHomologyFactors lam hfg z hJ hfin U hU hs 0) ≪≫
    supportedSequenceQuotientHomologyShiftNatIso lam hfg z hJ hfin U hU hs q ≪≫
    (supportedRankHomologyFactors lam hfg z hJ hfin U hU hs q).symm
  exact (Localization.fullyFaithfulWhiskeringLeft L W _).preimageIso eq

/-- Karoubi 包絡上でも次数別のホモロジーは第零ホモロジーのシフトである。 -/
noncomputable def completedSupportedHomologyShiftNatIso (q : ℤ) :
    shiftFunctor _ q ⋙ completedSupportedHomology lam hfg z hJ hfin U hU hs 0 ≅
      completedSupportedHomology lam hfg z hJ hfin U hU hs q := by
  let L := toKaroubi (SupportedSequenceRankQuotient (s := s) z)
  let F := completedSupportedHomology lam hfg z hJ hfin U hU hs 0
  let eq := isoWhiskerRight (L.commShiftIso q).symm F ≪≫
    isoWhiskerLeft (shiftFunctor _ q)
      (completedSupportedHomologyFactors lam hfg z hJ hfin U hU hs 0) ≪≫
    supportedRankHomologyShiftNatIso lam hfg z hJ hfin U hU hs q ≪≫
    (completedSupportedHomologyFactors lam hfg z hJ hfin U hU hs q).symm
  exact ((whiskeringLeft _ _ _).obj L).preimageIso eq

instance completedSupportedHomology_isHomological (q : ℤ) :
    (completedSupportedHomology lam hfg z hJ hfin U hU hs q).IsHomological := by
  dsimp only [completedSupportedHomology]
  infer_instance

end SerrePositivity.Asymptotic

end RankHomologyShiftNaturalPart
