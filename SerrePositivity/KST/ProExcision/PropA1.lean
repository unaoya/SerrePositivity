module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.ProExcision.BarRowComparison
public import SerrePositivity.KST.ProExcision.DiagonalFlip

/-!
# Proposition A.1 の幾何的比較

概要：群状単体的モノイドの作用に対し、E_BH G→B(G⋉H) は局所化で同型。
方針：各行を指定座標への作用の有限合成として示し、既存の対角の定理を適用する。
規約：KST Proposition A.1、GJ99 Proposition IV.1.9。Lemma A.2 はセル降下による既存の証明を使う。
使われ方：所有レーンの H_* の模型比較と Lemma A.4 の半直積への移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open SerrePositivity.KST.Comparison SerrePositivity.SimplicialModel SerrePositivity.BisimplicialModel
variable {G H : SimplicialObject MonCat.{u}}

/-- 概要：E_BH G から半直積の分類空間への比較は局所化で可逆。
方針：二重比較の各行の可逆性を対角へ移し、既存の transport 比較と同定する。
規約：KST Proposition A.1 の幾何的模型。H_* の新しい定義は導入しない。
使われ方：K-L2 の H_* を適用して原典の同型 (A.2) を得る。 -/
theorem actionBarComparison_localized_isIso (A : SimplicialMonoidAction G H)
    (hG : SimplicialMonoid.IsGrouplike G) :
    IsIso (AnodyneHomotopy.anodyneQ.map (actionBarComparison A)) := by
  let Q := AnodyneHomotopy.anodyneQ
  have hrows : ∀ n, IsIso (Q.map
      (((flipFunctor _ _ _).map (coefficientBisimplicialBarComparison A)).app n)) := by
    intro n
    exact coefficientBarRowComparison_localized_isIso A hG n.unop.len
  haveI := localized_diagonal_map_of_flipped_rows (coefficientBisimplicialBarComparison A) hrows
  have hd : IsIso (Q.map (Functor.whiskerLeft (Functor.diag SimplexCategoryᵒᵖ)
      (Functor.uncurry.map (coefficientBisimplicialBarComparison A)))) :=
    inferInstanceAs (IsIso (Q.map (diagonal.map (coefficientBisimplicialBarComparison A))))
  have hn := congrArg Q.map (coefficientBisimplicialBarComparison_diagonal A)
  simp only [CategoryTheory.Functor.map_comp] at hn
  have hc : IsIso (Q.map (coefficientBisimplicialBarDiagonalIso A).hom ≫
      Q.map (actionBarComparison A)) := hn.symm ▸ hd
  exact (isIso_comp_left_iff _ _).mp hc

/-- 概要：Proposition A.1 の比較の局所化における標準同型。
方針：実際の比較射を asIso で同型に束ねる。
規約：KST Proposition A.1、式 (A.2) の幾何的入力。
使われ方：借用する H_* の局所化上の関手を適用する。 -/
def propA1LocalizedComparisonIso (A : SimplicialMonoidAction G H)
    (hG : SimplicialMonoid.IsGrouplike G) :
    AnodyneHomotopy.anodyneQ.obj (coefficientActionBar A) ≅
      AnodyneHomotopy.anodyneQ.obj (monoidBar (simplicialActionProduct A)) :=
  letI := actionBarComparison_localized_isIso A hG
  asIso (AnodyneHomotopy.anodyneQ.map (actionBarComparison A))

/-- 概要：anodyne 射を反転する任意の関手は A.1 の比較を同型へ送る。
方針：実際に証明した局所化可逆性と局所化の普遍性を使う。
規約：KST Proposition A.1、式 (A.2)。F とその anodyne 不変性は H_* の所有レーンから借りる界面。
使われ方：H_i(G;C(H)) の模型が F(E_BH G) と与えられたときの原典の同型。 -/
theorem actionBarComparison_map_isIso {D : Type v} [Category.{w} D]
    (F : SSet.{u} ⥤ D) (hF : SSet.anodyneExtensions.IsInvertedBy F)
    (A : SimplicialMonoidAction G H) (hG : SimplicialMonoid.IsGrouplike G) :
    IsIso (F.map (actionBarComparison A)) :=
  AnodyneHomotopy.map_isIso_of_anodyneQ_isIso F hF _
    (actionBarComparison_localized_isIso A hG)

/-- 概要：所有レーンのホモロジー関手を受ける Proposition A.1 の標準同型。
方針：実際の比較の像を asIso に束ねる。
規約：KST Proposition A.1、非被約 C(H)。原典の (A.2) の両側の模型同定は F の所有レーンの界面。
使われ方：Lemma A.4 の係数写像と半直積写像を比較する。 -/
def propA1ComparisonIso {D : Type v} [Category.{w} D]
    (F : SSet.{u} ⥤ D) (hF : SSet.anodyneExtensions.IsInvertedBy F)
    (A : SimplicialMonoidAction G H) (hG : SimplicialMonoid.IsGrouplike G) :
    F.obj (coefficientActionBar A) ≅ F.obj (monoidBar (simplicialActionProduct A)) :=
  letI := actionBarComparison_map_isIso F hF A hG
  asIso (F.map (actionBarComparison A))

end SerrePositivity.KST.ProExcision

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KST "Eq (A.2)" (partial := component) "仮定：群状単体モノイドの作用と anodyne を反転する関手（Lean が強い：具体的な係数ホモロジーは別に入力）。結論：半直積 bar と作用付き bar の比較写像の局所化同型。原典の係数つき群ホモロジーの識別までは含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.ProExcision.actionBarComparison_localized_isIso
attribute [cite KST "Eq (A.2)" (partial := component) "仮定：群状単体モノイドの作用と anodyne を反転する関手（Lean が強い：具体的な係数ホモロジーは別に入力）。結論：半直積 bar と作用付き bar の比較写像の局所化同型。原典の係数つき群ホモロジーの識別までは含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.ProExcision.actionBarComparison_map_isIso
attribute [cite KST "Eq (A.3)" (partial := component) "仮定：群状単体モノイドの作用と anodyne を反転する関手（Lean が強い：具体的な係数ホモロジーは別に入力）。結論：半直積 bar と作用付き bar の比較写像の局所化同型。原典の係数つき群ホモロジーの識別までは含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.ProExcision.actionBarComparison_localized_isIso
attribute [cite KST "Eq (A.3)" (partial := component) "仮定：群状単体モノイドの作用と anodyne を反転する関手（Lean が強い：具体的な係数ホモロジーは別に入力）。結論：半直積 bar と作用付き bar の比較写像の局所化同型。原典の係数つき群ホモロジーの識別までは含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.ProExcision.actionBarComparison_map_isIso
attribute [cite KST "Prop A.1" (partial := component) "仮定：群状単体モノイドの作用と anodyne を反転する関手（Lean が強い：具体的な係数ホモロジーは別に入力）。結論：半直積 bar と作用付き bar の比較写像の局所化同型。原典の係数つき群ホモロジーの識別までは含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.ProExcision.actionBarComparison_localized_isIso
attribute [cite KST "Prop A.1" (partial := component) "仮定：群状単体モノイドの作用と anodyne を反転する関手（Lean が強い：具体的な係数ホモロジーは別に入力）。結論：半直積 bar と作用付き bar の比較写像の局所化同型。原典の係数つき群ホモロジーの識別までは含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.ProExcision.actionBarComparison_map_isIso
