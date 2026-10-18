module

public import SerrePositivity.KST.ProExcision.AdjacentCut
public import SerrePositivity.KST.ProExcision.ConeConnecting

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# 項濾過の任意区間と連結写像

概要：実際の項濾過の区間を、次数ごと分裂する商短完全列で表す。
方針：二重切り詰めの同型で短完全性を移し、濾過の δ の一般比較を適用する。
規約：有限添字への制限も同じ関手で扱い、添字の算術的等式による型変換を避ける。
使われ方：KST Lemma 4.10 の初頁微分と有限 Koszul 濾過。
-/

universe u v

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open SerrePositivity.StupidTruncation

variable {R : Type u} [CommRing R]

/-- 概要：二つの下端の間の項濾過の商を短複体にする。
方針：標準の商射を残し、第一射には実際の包含遷移を使う。
規約：b ≤ a。使われ方：KST Lemma 4.10 の有限添字での区間模型。 -/
def intervalCutShortComplex (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b : ℤ) (hab : b ≤ a) : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) := by
  let S := StupidTruncation.shortComplex (above P b) a
  refine ShortComplex.mk (truncationInclusion P a b hab) S.g ?_
  rw [← aboveAboveIso_inv_comp_inclusion P a b hab, Category.assoc]
  change (aboveAboveIso P a b hab).inv ≫ (S.f ≫ S.g) = 0
  rw [S.zero, comp_zero]

/-- 概要：区間短複体と標準切り詰め短複体の同型。
方針：第一項を二重切り詰めの逆同型で比較する。
規約：第二項と商は同一。使われ方：KST Lemma 4.10 の分裂と完全性の移送。 -/
def intervalCutIso (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b : ℤ) (hab : b ≤ a) :
    intervalCutShortComplex P a b hab ≅ StupidTruncation.shortComplex (above P b) a := by
  refine ShortComplex.isoMk (aboveAboveIso P a b hab).symm
    (Iso.refl _) (Iso.refl _) ?_ ?_
  · change (aboveAboveIso P a b hab).inv ≫ inclusion (above P b) a =
      truncationInclusion P a b hab ≫ 𝟙 _
    rw [Category.comp_id]
    exact aboveAboveIso_inv_comp_inclusion P a b hab
  · change 𝟙 _ ≫ (StupidTruncation.shortComplex (above P b) a).g =
      (StupidTruncation.shortComplex (above P b) a).g ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]

/-- 概要：区間短複体の次数ごとの分裂。
方針：標準切り詰めの分裂を区間同型に沿って移す。
規約：複体の分裂ではない。使われ方：KST Lemma 4.10 の δ の計算。 -/
def intervalCutSplitting (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b : ℤ) (hab : b ≤ a) (n : ℤ) :
    ((intervalCutShortComplex P a b hab).map (eval _ _ n)).Splitting :=
  (StupidTruncation.splitting (above P b) a n).ofIso
    ((eval (ModuleCat.{u} R) (.up ℤ) n).mapShortComplex.mapIso (intervalCutIso P a b hab).symm)

/-- 概要：任意の項濾過区間の短完全性。
方針：標準切り詰め短完全列との同型を使う。
規約：隣接性は不要。使われ方：KST Lemma 4.10 の商比較。 -/
theorem intervalCutShortComplex_shortExact
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ) (hab : b ≤ a) :
    (intervalCutShortComplex P a b hab).ShortExact :=
  ShortComplex.shortExact_of_iso (intervalCutIso P a b hab).symm
    (stupidTruncation_module_shortExact (above P b) a)

/-- 概要：全テンソル後の項濾過区間。
方針：区間短複体を同じ右テンソル関手で写す。
規約：任意の係数複体。使われ方：KST Lemma 4.10 の実際の濾過。 -/
def intervalTensorCutShortComplex (P K : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b : ℤ) (hab : b ≤ a) : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  cochainTensorShortComplexRight (intervalCutShortComplex P a b hab) K

/-- 概要：全テンソル後の区間短複体の次数ごとの分裂。
方針：元の区間分裂をテンソルで写す。
規約：平坦性は不要。使われ方：KST Lemma 4.10 の区間境界。 -/
def intervalTensorCutSplitting (P K : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b : ℤ) (hab : b ≤ a) (n : ℤ) :
    ((intervalTensorCutShortComplex P K a b hab).map (eval _ _ n)).Splitting :=
  cochainTensorShortComplexRightSplitting (intervalCutShortComplex P a b hab)
    (intervalCutSplitting P a b hab) K n

/-- 概要：全テンソル後の任意区間は短完全。
方針：次数ごとの分裂を用いる。
規約：係数複体の平坦性は不要。使われ方：KST Lemma 4.10 の cone–商比較。 -/
theorem intervalTensorCutShortComplex_shortExact
    (P K : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ) (hab : b ≤ a) :
    (intervalTensorCutShortComplex P K a b hab).ShortExact :=
  cochainTensorShortComplexRight_shortExact (intervalCutShortComplex P a b hab)
    (intervalCutSplitting P a b hab) K

/-- 概要：再添字したテンソル項濾過の射に、その実際の商短複体を割り当てる。
方針：再添字関手が与える下端をそのまま使う。
規約：Koszul の有限添字への制限を含む。使われ方：KST Lemma 4.10 の微分比較。 -/
def tensorFiltrationInterval {I : Type v} [Preorder I]
    (P K : CochainComplex (ModuleCat.{u} R) ℤ) (index : I ⥤ ℤ)
    {i j : I} (f : i ⟶ j) : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  intervalTensorCutShortComplex P K (-index.obj i) (-index.obj j)
    (neg_le_neg (index.map f).le)

/-- 概要：再添字テンソル項濾過の区間の明示的なシフトつき境界。
方針：実際の区間短複体の次数ごとの分裂から境界を作る。
規約：複体の分裂は仮定しない。使われ方：KST Lemma 4.10 の初頁微分を簡潔に記述する。 -/
def tensorFiltrationBoundary {I : Type v} [Preorder I]
    (P K : CochainComplex (ModuleCat.{u} R) ℤ) (index : I ⥤ ℤ)
    {i j : I} (f : i ⟶ j) :
    (tensorFiltrationInterval P K index f).X₃ ⟶
      (tensorFiltrationInterval P K index f).X₁⟦(1 : ℤ)⟧ :=
  CochainComplex.homOfDegreewiseSplit (tensorFiltrationInterval P K index f)
    (intervalTensorCutSplitting P K (-index.obj i) (-index.obj j)
      (neg_le_neg (index.map f).le))


end SerrePositivity.KST.ProExcision
