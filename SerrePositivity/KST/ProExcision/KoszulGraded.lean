module

public import SerrePositivity.KST.ProExcision.TruncationNaturality
public import SerrePositivity.HomologicalAlgebra.BoundedTermKoszulAcyclic
public import SerrePositivity.HomologicalAlgebra.CochainTensorShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.SpectralObject.FirstPage

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# Koszul 項濾過の次数別商

概要：有限 Koszul 濾過の連続する項の商を一項複体へ比較する。
方針：既存の次数ごと分裂する短完全列と mapping cone の比較を使う。
規約：補助スペクトル系列の初頁と KST の E₂ 頁を混同しない。
使われ方：KST Lemma 4.10 の初頁計算の準備。
-/

universe u

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open SerrePositivity.StupidTruncation

variable {R : Type u} [CommRing R]

/-- 概要：項濾過の次数別商は、その次数の項だけを持つ複体。
方針：下端で切ってから同じ次数で上端を切る。
規約：同型は元の項の標準同型を用いる。使われ方：KST Lemma 4.10 の初頁。 -/
def truncationGradeIso (P : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    below (above P a) a ≅ (CochainComplex.singleFunctor (ModuleCat.{u} R) a).obj (P.X a) :=
  stupidTruncation_belowSingleIso (above P a) a (fun q hq ↦ above_isZero_X P a q hq) ≪≫
    (CochainComplex.singleFunctor (ModuleCat.{u} R) a).mapIso (aboveXIso P a a (le_refl a))

/-- 概要：連続する切り詰めと商の短複体を係数複体とテンソルする。
方針：既存の次数ごと分裂する切り詰め短複体を使う。
規約：係数複体の平坦性は不要。使われ方：KST Lemma 4.10 の濾過の次数別商。 -/
def tensorCutShortComplex (P K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  cochainTensorShortComplexRight (StupidTruncation.shortComplex (above P a) (a + 1)) K

/-- 概要：テンソル後の切り詰め短複体は短完全。
方針：各次数の分裂が全テンソルで保たれることを使う。
規約：通常のテンソルが任意の短完全列を保つとは仮定しない。
使われ方：KST Lemma 4.10 の初頁の cone と商の比較。 -/
theorem tensorCutShortComplex_shortExact
    (P K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    (tensorCutShortComplex P K a).ShortExact :=
  cochainTensorShortComplexRight_shortExact
    (StupidTruncation.shortComplex (above P a) (a + 1))
    (StupidTruncation.splitting (above P a) (a + 1)) K

/-- 概要：切り詰めの cone から次数別商への標準射。
方針：短複体から mapping cone の比較射を構成する。
規約：実際の複体射を固定する。使われ方：KST Lemma 4.10 の初頁同定。 -/
def tensorCutConeComparison (P K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    CochainComplex.mappingCone (tensorCutShortComplex P K a).f ⟶
      (tensorCutShortComplex P K a).X₃ :=
  CochainComplex.mappingCone.descShortComplex (tensorCutShortComplex P K a)

/-- 概要：cone と次数別商の比較射は擬同型。
方針：実際の短完全列の mapping cone 比較を適用する。
規約：全次数のホモロジーで同型。使われ方：KST Lemma 4.10 の初頁計算。 -/
theorem tensorCutConeComparison_quasiIso
    (P K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    QuasiIso (tensorCutConeComparison P K a) :=
  CochainComplex.mappingCone.quasiIso_descShortComplex (tensorCutShortComplex_shortExact P K a)

/-- 概要：テンソル後の次数別商は、一項複体をテンソルしたもの。
方針：切り詰め商の標準同型をテンソル関手で写す。
規約：次数 a の符号を保持する。使われ方：KST Lemma 4.10 の初頁の係数計算。 -/
def tensorCutGradeIso (P K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    (tensorCutShortComplex P K a).X₃ ≅
      cochainTensor ((CochainComplex.singleFunctor (ModuleCat.{u} R) a).obj (P.X a)) K := by
  change cochainTensor (below (above P a) (a + 1 - 1)) K ≅ _
  rw [add_sub_cancel_right]
  exact (cochainTensorFixedRight K).mapIso (truncationGradeIso P a)

/-- 概要：cone のホモロジーを一項複体のテンソルのホモロジーへ同定する。
方針：cone 比較の擬同型と次数別商の同型を合成する。
規約：任意のコホモロジー次数 q。使われ方：KST Lemma 4.10 の初頁計算。 -/
def tensorCutConeHomologyIso (P K : CochainComplex (ModuleCat.{u} R) ℤ) (a q : ℤ) :
    (CochainComplex.mappingCone (tensorCutShortComplex P K a).f).homology q ≅
      (cochainTensor
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) a).obj (P.X a)) K).homology q := by
  have : QuasiIso (tensorCutConeComparison P K a) := tensorCutConeComparison_quasiIso P K a
  exact isoOfQuasiIsoAt (tensorCutConeComparison P K a) q ≪≫
    (homologyFunctor _ _ q).mapIso (tensorCutGradeIso P K a)

/-- 概要：二重切り詰めの標準同型は元の複体への包含と可換。
方針：切り詰め写像の自然性に帰着する。
規約：b ≤ a。使われ方：Koszul 濾過の隣接射の cone 比較。 -/
theorem aboveAboveIso_comp_inclusion (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b : ℤ) (hab : b ≤ a) :
    (aboveAboveIso P a b hab).hom ≫ inclusion P a =
      inclusion (above P b) a ≫ inclusion P b :=
  truncationMap_comp_inclusion (inclusion P b) a

/-- 概要：二重切り詰めの逆同型は実際の包含遷移を与える。
方針：元の複体への包含で相殺する。
規約：実際の複体射の等式。使われ方：KST Lemma 4.10 の初頁計算。 -/
theorem aboveAboveIso_inv_comp_inclusion (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b : ℤ) (hab : b ≤ a) :
    (aboveAboveIso P a b hab).inv ≫ inclusion (above P b) a =
      truncationInclusion P a b hab := by
  have : Mono (inclusion P b) := mono_of_mono_f _ (fun _ ↦ inferInstance)
  apply (cancel_mono (inclusion P b)).mp
  rw [Category.assoc, ← aboveAboveIso_comp_inclusion P a b hab,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp, truncationInclusion_comp_inclusion]

/-- 概要：隣接する項濾過の cone は短完全列の cone と同型。
方針：二重切り詰めの標準同型から射の同型を作り cone 関手で写す。
規約：テンソル後の実際の隣接射を使用する。
使われ方：KST Lemma 4.10 のスペクトル対象と次数別商の比較。 -/
def adjacentTensorConeIso (P K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    CochainComplex.mappingCone ((cochainTensorFixedRight K).map
      (truncationInclusion P (a + 1) a (by omega))) ≅
      CochainComplex.mappingCone (tensorCutShortComplex P K a).f := by
  let e := (aboveAboveIso P (a + 1) a (by omega)).symm
  let F := cochainTensorFixedRight K
  let iso : ComposableArrows.mk₁ (F.map (truncationInclusion P (a + 1) a (by omega))) ≅
      ComposableArrows.mk₁ (tensorCutShortComplex P K a).f :=
    ComposableArrows.isoMk₁ (F.mapIso e) (Iso.refl _) (by
      symm
      change F.map e.hom ≫ F.map (inclusion (above P a) (a + 1)) =
        F.map (truncationInclusion P (a + 1) a _) ≫ 𝟙 _
      rw [← F.map_comp, Category.comp_id]
      exact congrArg F.map (aboveAboveIso_inv_comp_inclusion P (a + 1) a _))
  exact (HomotopyCategory.composableArrowsFunctor (ModuleCat.{u} R)).mapIso iso

/-- 概要：項濾過の隣接射の cone のホモロジーは、その項のテンソルで計算できる。
方針：隣接 cone の同型と次数別商の擬同型を合成する。
規約：全テンソル複体の段階で比較する。使われ方：KST Lemma 4.10 の初頁同定。 -/
def adjacentTensorConeHomologyIso
    (P K : CochainComplex (ModuleCat.{u} R) ℤ) (a q : ℤ) :
    (CochainComplex.mappingCone ((cochainTensorFixedRight K).map
      (truncationInclusion P (a + 1) a (by omega)))).homology q ≅
      (cochainTensor
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) a).obj (P.X a)) K).homology q :=
  (homologyFunctor _ _ q).mapIso (adjacentTensorConeIso P K a) ≪≫
    tensorCutConeHomologyIso P K a q

/-- 概要：有限行のスペクトル系列の初頁はスペクトル対象の区間ホモロジー。
方針：初頁の外側添字と内側添字の一致を計算する。
規約：Mathlib の頁番号 2。使われ方：KST Lemma 4.10 の補助初頁計算。 -/
instance finiteFirstPageComputation (l : ℕ) :
    (Abelian.SpectralObject.coreE₂CohomologicalFin l).HasFirstPageComputation where
  hi₀₁ pq := by
    apply Fin.ext
    simp [Abelian.SpectralObject.coreE₂CohomologicalFin]
  hi₂₃ pq := by
    apply Fin.ext
    simp [Abelian.SpectralObject.coreE₂CohomologicalFin, Fin.clamp]

/-- 概要：Koszul 補助スペクトル系列の初頁を区間ホモロジーで表す。
方針：有限行の初頁計算を実際の Koszul スペクトル対象に適用する。
規約：この初頁自体を KST の E₂ と呼ばない。
使われ方：KST Lemma 4.10 の初頁と次頁の同定の出発点。 -/
def koszulFirstPageXIso {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (pq : ℤ × Fin (e + 1)) :
    ((koszulFilteredSpectralSequence z K).page 2).X pq ≅
      ((koszulFilteredSpectralObject z K).H (pq.1 + (pq.2.val : ℤ))).obj
        (ComposableArrows.mk₁ (homOfLE (show pq.2.castSucc ≤ pq.2.succ by
          simp [Fin.le_iff_val_le_val]))) :=
  (koszulFilteredSpectralObject z K).spectralSequenceFirstPageXIso
    (Abelian.SpectralObject.coreE₂CohomologicalFin (e + 1)) pq _ _ rfl rfl _ rfl

end SerrePositivity.KST.ProExcision
