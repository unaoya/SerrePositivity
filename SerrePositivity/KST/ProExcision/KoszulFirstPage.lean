module

public import SerrePositivity.KST.ProExcision.KoszulGraded
public import SerrePositivity.HomologicalAlgebra.CochainTensorSingle

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

/-!
# Koszul 補助初頁の係数

概要：濾過区間と一項複体のホモロジーを具体的な係数加群へ比較する。
方針：mapping cone、ホモトピー圏のホモロジー、シフト、平坦テンソルの自然同型を合成する。
規約：本ファイルの補助初頁の微分を取った後の頁と KST の E₂ を比較する。
使われ方：KST Lemma 4.10 の Koszul スペクトル系列の初頁計算。
-/

universe u v w

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex

variable {R : Type u} [CommRing R]

/-- 概要：任意の濾過複体から実際のホモロジースペクトル対象を構成する。
方針：mapping cone スペクトル対象を引き戻してホモロジーを取る。
規約：収束は別に証明する。使われ方：KST Lemma 4.10 の区間計算。 -/
def filteredHomologySpectralObject {I : Type v} [Category.{w} I]
    (F : I ⥤ CochainComplex (ModuleCat.{u} R) ℤ) :
    Abelian.SpectralObject (ModuleCat.{u} R) I :=
  ((HomotopyCategory.spectralObjectMappingCone (ModuleCat.{u} R)).precomp F).mapHomologicalFunctor
     (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0)

/-- 概要：濾過の区間ホモロジーは、その区間の射の cone のホモロジー。
方針：mapping cone スペクトル対象とホモトピー圏のホモロジーの比較を使う。
規約：任意の添字圏と濾過関手。使われ方：KST Lemma 4.10 の初頁モデルの接続。 -/
def filtrationIntervalHomologyIso {I : Type v} [Category.{w} I]
    (F : I ⥤ CochainComplex (ModuleCat.{u} R) ℤ) {i j : I} (f : i ⟶ j) (q : ℤ) :
    ((filteredHomologySpectralObject F).H q).obj
        (ComposableArrows.mk₁ f) ≅ (CochainComplex.mappingCone (F.map f)).homology q :=
  (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} R) (.up ℤ) q).app _

/-- 概要：次数 a の一項複体との全テンソルを、点ごとのテンソルのシフトへ同定する。
方針：一項複体のシフト、全テンソルのシフト、零度の比較を合成する。
規約：シフトは -a。使われ方：KST Lemma 4.10 の初頁の次数計算。 -/
def singleTensorShiftIso (M : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    cochainTensor ((CochainComplex.singleFunctor (ModuleCat.{u} R) a).obj M) K ≅
      (((tensorLeft M).mapHomologicalComplex (.up ℤ)).obj K)⟦-a⟧ :=
  (cochainTensorFixedRight K).mapIso
    (((CochainComplex.singleFunctors (ModuleCat.{u} R)).shiftIso (-a) a 0 (by omega)).app M).symm ≪≫
    cochainTensorShiftLeft (cochainSingleZero M) K (-a) ≪≫
    (shiftFunctor _ (-a : ℤ)).mapIso (cochainTensorSingleLeftIso M K)

/-- 概要：平坦な左テンソル関手とホモロジーの自然同型。
方針：平坦性による完全性を短複体のホモロジーに適用する。
規約：係数 M は R 加群として平坦。使われ方：KST Lemma 4.10 の自由な Koszul 項。 -/
def flatLeftTensorHomologyIso (M : ModuleCat.{u} R) [Module.Flat R M] (q : ℤ) :
    (tensorLeft M).mapHomologicalComplex (.up ℤ) ⋙ homologyFunctor _ _ q ≅
      homologyFunctor _ _ q ⋙ tensorLeft M := by
  let : (tensorLeft M).PreservesHomology := Functor.preservesHomologyOfExact _
  exact NatIso.ofComponents (fun K ↦ (K.sc q).mapHomologyIso (tensorLeft M))
    (fun f ↦ ShortComplex.mapHomologyIso_hom_naturality
      ((shortComplexFunctor _ _ q).map f) (tensorLeft M))

/-- 概要：平坦な一項複体のテンソルのホモロジーは、係数とシフトしたホモロジーのテンソル。
方針：全テンソルのシフト比較と平坦テンソルのホモロジー保存を合成する。
規約：次数 q は q-a に移る。使われ方：KST Lemma 4.10 の初頁の項。 -/
def singleTensorHomologyIso (M : ModuleCat.{u} R) [Module.Flat R M]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a q : ℤ) :
    (cochainTensor ((CochainComplex.singleFunctor (ModuleCat.{u} R) a).obj M) K).homology q ≅
      (tensorLeft M).obj (K.homology (q - a)) :=
  (homologyFunctor _ _ q).mapIso (singleTensorShiftIso M K a) ≪≫
    ((CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} R)
      (-a) q (q - a) (by omega)).app _) ≪≫
    (flatLeftTensorHomologyIso M (q - a)).app K

/-- 概要：Koszul 補助初頁を隣接濾過射の cone のホモロジーへ同定する。
方針：初頁の区間表示とホモトピー圏のホモロジー比較を合成する。
規約：Mathlib の初頁番号 2。使われ方：KST Lemma 4.10 の具体的な初頁計算。 -/
def koszulFirstPageConeIso {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (pq : ℤ × Fin (e + 1)) :
    ((koszulFilteredSpectralSequence z K).page 2).X pq ≅
      (CochainComplex.mappingCone ((finiteKoszulTensorFiltration z K).map
        (homOfLE (show pq.2.castSucc ≤ pq.2.succ by
          simp [Fin.le_iff_val_le_val])))).homology (pq.1 + (pq.2.val : ℤ)) :=
  koszulFirstPageXIso z K pq ≪≫
    filtrationIntervalHomologyIso (finiteKoszulTensorFiltration z K) _ _

/-- 概要：切り詰めの下端の等しい表示はテンソル cone の同型を与える。
方針：添字の等式で置換し、恒等同型を取る。
規約：依存する射の型の変更を同型として明示する。使われ方：有限濾過の添字の正規化。 -/
def truncationTensorConeIsoOfEq (P K : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b a' b' : ℤ) (h : b ≤ a) (h' : b' ≤ a') (ha : a = a') (hb : b = b') :
    CochainComplex.mappingCone ((tensorRight K).map (truncationInclusion P a b h)) ≅
      CochainComplex.mappingCone ((tensorRight K).map (truncationInclusion P a' b' h')) := by
  subst a'
  subst b'
  exact Iso.refl _

/-- 概要：Koszul 補助初頁を、その Koszul 項の一項複体のテンソルで計算する。
方針：有限濾過の隣接射を整数添字の切り詰めに展開する。
規約：p 行の Koszul 項は -p 次。使われ方：KST Lemma 4.10 の初頁の係数。 -/
def koszulFirstPageSingleIso {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (pq : ℤ × Fin (e + 1)) :
    ((koszulFilteredSpectralSequence z K).page 2).X pq ≅
      (cochainTensor
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) (-(pq.2.val : ℤ))).obj
          ((koszulComplex z).X (-(pq.2.val : ℤ)))) K).homology
            (pq.1 + (pq.2.val : ℤ)) := by
  refine koszulFirstPageConeIso z K pq ≪≫ ?_
  refine (homologyFunctor _ _ _).mapIso
    (truncationTensorConeIsoOfEq (koszulComplex z) K
      (-((pq.2.val : ℤ) - 1)) (-(((pq.2.val + 1 : ℕ) : ℤ) - 1))
      (-(pq.2.val : ℤ) + 1) (-(pq.2.val : ℤ))
      (by omega) (by omega) (by omega) (by omega)) ≪≫ ?_
  exact adjacentTensorConeHomologyIso (koszulComplex z) K (-(pq.2.val : ℤ))
    (pq.1 + (pq.2.val : ℤ))

/-- 概要：Koszul 補助初頁の係数を、Koszul 項と K のホモロジーのテンソルで表す。
方針：Koszul 項の自由性と平坦性を使い、一項複体のシフト比較を適用する。
規約：位置 (s,p) の K の次数は s+2p。使われ方：KST Lemma 4.10 の E₁ 項。 -/
def koszulFirstPageTermIso {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (pq : ℤ × Fin (e + 1)) :
    ((koszulFilteredSpectralSequence z K).page 2).X pq ≅
      (tensorLeft ((koszulComplex z).X (-(pq.2.val : ℤ)))).obj
        (K.homology (pq.1 + (pq.2.val : ℤ) + (pq.2.val : ℤ))) := by
  let : Module.Free R ((koszulComplex z).X (-(pq.2.val : ℤ))) :=
    (koszulComplex_free_finite_X z (-(pq.2.val : ℤ))).1
  refine koszulFirstPageSingleIso z K pq ≪≫ ?_
  simpa only [sub_neg_eq_add] using
    singleTensorHomologyIso ((koszulComplex z).X (-(pq.2.val : ℤ))) K
      (-(pq.2.val : ℤ)) (pq.1 + (pq.2.val : ℤ))

/-- 概要：KST のホモロジー添字で補助初頁の係数を表す。
方針：Mathlib の位置を (−q−2p,p) と再添字する。
規約：補助頁 2 は KST の E₁。使われ方：KST Lemma 4.10 の E₂ 同定の前段。 -/
def koszulFirstPageHomologicalTermIso {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (p : Fin (e + 1)) (q : ℤ) :
    ((koszulFilteredSpectralSequence z K).page 2).X (-q - 2 * (p.val : ℤ), p) ≅
      (tensorLeft ((koszulComplex z).X (-(p.val : ℤ)))).obj (K.homology (-q)) := by
  have h : -q - 2 * (p.val : ℤ) + (p.val : ℤ) + (p.val : ℤ) = -q := by omega
  simpa only [h] using koszulFirstPageTermIso z K (-q - 2 * (p.val : ℤ), p)

/-- 概要：補助頁の微分の次数は KST の一つ前の頁の微分の次数に対応する。
方針：(s,p) ↦ (p,−s−2p) の式を計算する。
規約：Mathlib r 頁は KST r−1 頁。使われ方：KST Lemma 4.10 の頁番号の対応。 -/
theorem kst_reindex_differential_degree (s p r : ℤ) :
    -(s + r) - 2 * (p + 1 - r) = (-s - 2 * p) + (r - 2) := by omega

end SerrePositivity.KST.ProExcision
