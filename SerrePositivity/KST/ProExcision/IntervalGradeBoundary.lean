module

public import SerrePositivity.KST.ProExcision.GradedHomology
public import SerrePositivity.KST.ProExcision.IntervalCut

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# 区間の添字の正規化と隣接境界

概要：有限濾過の実際の三つの下端を、隣接次数の商模型へ比較する。
方針：下端の等式による同型を明示し、分裂境界も同じ等式で移す。
規約：依存する複体の型変換を暗黙の算術簡約に任せない。
使われ方：KST Lemma 4.10 の有限 Koszul 初頁微分。
-/

universe u

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex

variable {R : Type u} [CommRing R]

/-- 概要：実際の二つの区間下端が隣接する場合、その短複体を隣接模型へ移す。
方針：二つの下端の等式で置換し恒等同型を使う。
規約：第三引数 c が商の残る次数。使われ方：KST Lemma 4.10 の有限添字の正規化。 -/
def intervalTensorAdjacentIso (P K : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b c : ℤ) (hab : b ≤ a) (ha : a = c + 1) (hb : b = c) :
    intervalTensorCutShortComplex P K a b hab ≅ adjacentTensorCutShortComplex P K c := by
  subst a
  subst b
  exact Iso.refl _

/-- 概要：三つの下端から作る二つの商の間のシフト境界。
方針：右の区間短複体の境界に左の商射のシフトを合成する。
規約：c ≤ b ≤ a。使われ方：KST Lemma 4.10 の有限濾過の δ の商模型。 -/
def intervalTensorGradeBoundary (P K : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b c : ℤ) (hab : b ≤ a) (hbc : c ≤ b) :
    (intervalTensorCutShortComplex P K b c hbc).X₃ ⟶
      (intervalTensorCutShortComplex P K a b hab).X₃⟦(1 : ℤ)⟧ :=
  CochainComplex.homOfDegreewiseSplit (intervalTensorCutShortComplex P K b c hbc)
    (intervalTensorCutSplitting P K b c hbc) ≫
      (intervalTensorCutShortComplex P K a b hab).g⟦(1 : ℤ)⟧'

/-- 概要：隣接する三つの下端の区間境界は、正規化後の隣接商境界と一致。
方針：下端の等式で置換し、同じ標準分裂から作った射を比較する。
規約：商同型を前後に明示する。使われ方：KST Lemma 4.10 の実際の初頁微分の正規化。 -/
theorem intervalTensorGradeBoundary_adjacent
    (P K : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b c : ℤ) (hab : b ≤ a) (hbc : c ≤ b)
    (ha : a = (c + 1) + 1) (hb : b = c + 1) :
    intervalTensorGradeBoundary P K a b c hab hbc ≫
      ((ShortComplex.π₃.mapIso
        (intervalTensorAdjacentIso P K a b (c + 1) hab ha hb)).hom)⟦(1 : ℤ)⟧' =
      (ShortComplex.π₃.mapIso (intervalTensorAdjacentIso P K b c c hbc hb rfl)).hom ≫
        adjacentTensorGradeBoundary P K c := by
  subst a
  subst b
  simp only [intervalTensorAdjacentIso, Functor.mapIso_refl, Iso.refl_hom,
    Category.id_comp]
  rfl

/-- 概要：任意表示の隣接区間の商ホモロジーを、指定次数の係数模型へ移す。
方針：下端の等式で隣接模型へ移し、そのホモロジー比較を合成する。
規約：平坦性は残る c 次の項だけ。使われ方：KST Lemma 4.10 の実際の有限初頁の係数模型。 -/
def intervalTensorGradeHomologyIso
    (P K : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b c q s : ℤ) (hab : b ≤ a) (ha : a = c + 1) (hb : b = c)
    [Module.Flat R (P.X c)] (hs : q - c = s) :
    (intervalTensorCutShortComplex P K a b hab).X₃.homology q ≅
      (tensorLeft (P.X c)).obj (K.homology s) :=
  (homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).mapIso
      (ShortComplex.π₃.mapIso (intervalTensorAdjacentIso P K a b c hab ha hb)) ≪≫
    adjacentTensorGradeHomologyIso P K c q s hs

/-- 概要：実際の三つの隣接下端の境界は、係数模型上で元の微分のテンソルを誘導する。
方針：下端を正規化して隣接商のホモロジー微分の定理を適用する。
規約：源と標的の係数次数は共通。使われ方：KST Lemma 4.10 の有限 Koszul 初頁微分。 -/
theorem intervalTensorGradeHomology_differential
    (P K : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b c c₀ d q q' s : ℤ) (hab : b ≤ a) (hbc : c ≤ b)
    (ha : a = d + 1) (hb : b = d) (hc : c = c₀) (hd : c₀ + 1 = d)
    [Module.Flat R (P.X c₀)] [Module.Flat R (P.X d)]
    (hq : q + 1 = q') (hs : q - c₀ = s) :
    (homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).shiftMap
        (intervalTensorGradeBoundary P K a b c hab hbc) q q' (by omega) ≫
      (intervalTensorGradeHomologyIso P K a b d q' s hab ha hb (by omega)).hom =
      (intervalTensorGradeHomologyIso P K b c c₀ q s hbc (by omega) hc hs).hom ≫
        (P.d c₀ d ▷ K.homology s) := by
  subst c
  subst d
  subst a
  subst b
  simp only [intervalTensorGradeHomologyIso, intervalTensorAdjacentIso, Functor.mapIso_refl]
  erw [Functor.mapIso_refl, Functor.mapIso_refl]
  erw [Iso.refl_trans, Iso.refl_trans]
  exact adjacentTensorGradeHomology_differential P K c₀ q q' s hq hs

end SerrePositivity.KST.ProExcision
