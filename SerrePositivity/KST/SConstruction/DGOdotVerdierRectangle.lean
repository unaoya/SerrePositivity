module
public import SerrePositivity.KST.SConstruction.DGOdotLaxVerdierConnection

/-!
概要：未供給の S 内零化と全長方形を明示入力に保ち、同じ d8 へ接続する。
方針：Sp 正本の相対長方形を具体的な dg 二射へ特殊化する。
規約：対象別 ε の収縮から S 内の自然な零化を作らない。
使われ方：D2・β3・Sp-6 の供給後も同じ入力と境界を保つ形式的接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra InfinityCategories LocalizingInvariants
open scoped Simplicial
variable {R : Type u} [CommRing R] {d : DGOdotInput R}

/-- 概要：Sp-6 が供給する S 内の全長方形を隔離する。
方針：指定全単体の ν 像と元の左端の頂点を保持する。
規約：存在を主張しない。使われ方：同じ相対 E と元の dg 入力の接続。 -/
structure DGOdotVerdierRectangleInput (h : DGOdotLaxVerdierInput R d) where
  diagram : (Δ[2] ⊗ Δ[1] : SSet.{u + 2}) ⟶ dgKInputInfinity.{u, u + 1} R
  image_eq : diagram ≫ dgKInputNu R =
    (LaxUniversalDifference.rectangle (dgOdotLowerExactMap R d) (dgOdotUpperExactMap R d)
      h.inclusion h.projection h.isVerdier).diagram
  source_vertex : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex ((β_ (Δ[1] : SSet.{u + 2}) Δ[1]).hom ≫
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare diagram 2) 0 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotDiagonalSourceInput R d)

namespace DGOdotVerdierRectangleInput
variable {h : DGOdotLaxVerdierInput R d} (t : DGOdotVerdierRectangleInput h)

/-- 概要：同じ長方形の右面と外周を相対 Verdier 提示にする。
方針：Sp 正本の構成を適用する。規約：長方形を選び直さない。
使われ方：二つの fiber 四角形の消去。 -/
def relativeRectangle : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierRectangle (dgKInputNu.{u, u + 1} R) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.relativeRectangle (dgKInputNu R)
    (dgOdotLowerExactMap R d) (dgOdotUpperExactMap R d)
    h.inclusion h.projection h.isVerdier t.diagram t.image_eq

/-- 概要：元の長方形から取り出す S 内の比較四角形。
方針：同じ相対長方形の左面を使う。規約：ν 像だけへ置換しない。
使われ方：元の E を後合成する四角形。 -/
def comparisonSquare : (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ dgKInputInfinity.{u, u + 1} R :=
  t.relativeRectangle.comparisonSquare

/-- 概要：同じ全比較四角形の ν 像。方針：既存の相対 Tamme 照合を使う。
規約：四辺だけの照合で代用しない。使われ方：元の d8 の回収。 -/
lemma comparison_image : t.comparisonSquare ≫ dgKInputNu R =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.comparisonSquare (dgOdotLowerExactMap R d)
      (dgOdotUpperExactMap R d) h.inclusion h.projection h.isVerdier :=
  dgKRelativeTammeComparison_image R _ _ h.inclusion h.projection h.isVerdier
    t.diagram t.image_eq

/-- 概要：比較四角形の左下頂点は元の dg 対角始域。
方針：入力した同じ頂点等式を保持する。規約：ν 像での一致だけではない。
使われ方：元の不変量値を極限錐の頂点にする。 -/
lemma comparison_source : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.comparisonSquare 0 0 =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotDiagonalSourceInput R d) := t.source_vertex

/-- 概要：同じ包含辺の ν 像を保持する。方針：全四角形の像から制限する。
規約：S 内で未供給の包含 lift は主張しない。使われ方：元の左射の照合。 -/
lemma comparison_bottom_image : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ t.comparisonSquare ≫ dgKInputNu R =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow h.inclusion).edge := by
  rw [t.comparison_image]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.comparisonSquare_bottom _ _ _ _ _

/-- 概要：相対不変量は同じ四角形を pullback に送る。
方針：二つの相対 Verdier 面を Sp 正本で消去する。
規約：K の局所化性や E の絶対延長は仮定しない。使われ方：K-10 d の形式的結論。 -/
lemma comparison_isPullback {E : dgKInputInfinity.{u, u + 1} R ⟶ Sp.{u + 1}}
    (hE : IsDGKRelativeLocalizingInvariant R E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (t.comparisonSquare ≫ E) :=
  (_root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.comparisonSquare_isPullback t.relativeRectangle) hE

/-- 概要：同じ E 値の右面を fiber 三角形にする。
方針：Sp 正本の相対列を適用する。規約：元の全零化面を保持する。
使われ方：長方形の二つの fiber 列との接続。 -/
lemma right_isFiber {E : dgKInputInfinity.{u, u + 1} R ⟶ Sp.{u + 1}}
    (hE : IsDGKRelativeLocalizingInvariant R E) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence (hE.fiberTriangle t.relativeRectangle.right) :=
  hE.fiberTriangle_isFiber t.relativeRectangle.right

/-- 概要：同じ比較四角形の実極限錐。方針：Sp 正本の pullback 錐を使う。
規約：候補錐を無条件な極限としない。使われ方：元の値の錐への接続。 -/
def comparisonCone (E : dgKInputInfinity.{u, u + 1} R ⟶ Sp.{u + 1}) :=
  (_root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.comparisonCone t.relativeRectangle) E

/-- 概要：指定された同じ比較錐は実際に極限。
方針：相対局所化条件を既存定理へ渡す。規約：未供給入力を省略しない。
使われ方：Cat^perf 版の次工程への形式的出力。 -/
lemma comparisonCone_isLimit {E : dgKInputInfinity.{u, u + 1} R ⟶ Sp.{u + 1}}
    (hE : IsDGKRelativeLocalizingInvariant R E) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (t.comparisonCone E) :=
  (_root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.comparisonCone_isLimit t.relativeRectangle) hE

end DGOdotVerdierRectangleInput
end SerrePositivity.KST.SConstruction
