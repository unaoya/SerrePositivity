module
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeLiftNu
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisIdentityNative

/-!
概要：実中央射の二段小基底と実差の終域を、同じ resolved 商の固定 ν 値へ照合する。
方針：二像・逆回転の元実包絡評価を合成し、元二成分の全 ν 比較を回収する。
規約：元比較射・実中央射を変更しない。D2 の全 lax 比較は別工程。
使われ方：共通 S 長方形の右面を LT の同じ商頂点へ接続する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "B" => DGOdotGluing R d
local notation "P" => DGCategoryCellResolution.Source R (B)
local notation "Q" => DGQuotient.QuotientObject (P)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (B)
    (dgQuotientImage R (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d))))
local notation "F" => dgOdotMilnorRightAxisQuotientSource R d
local notation "G" => dgOdotMilnorRightAxisQuotientTarget R d
local notation "X" => dgPerfectComparisonFamily R (Q) (F) (G)
local notation "T" => DGPerfectComparisonBase R (Q) (F) (G)
local notation "I" => DGFunctor.id (T)
local notation "H" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R (T) (T) (dgHomGluingBimodule R (T) (T) (T) (I) (I))
local notation "Y" => dgHomGluingLoopConeFamily R (T) (T) (T) (I) (I)
local notation "U" => DGOdotMilnorRightAxisBase R d
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (B) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnor_isDGPretriangulated R d
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (P) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated R (B)

/-- 概要：同じ二実像包絡の固定 ν 頂点。
方針：元の二成分を含む同じ小模型を持ち上げる。
規約：同型な代表へ置換しない。使われ方：二段評価の中間頂点。 -/
def dgOdotMilnorRightAxisComparisonBaseInput : PerfDGInput.{u, u + 1} R :=
  dgKUniverseInput.{u, u + 1, u + 1} R (T)

/-- 概要：元二実像小基底の ν 値と同じ resolved 商 ν 値の指定同値。
方針：同じ包絡の実包含・Perf 評価を使用する。
規約：同じ商を保持。使われ方：元二成分の終域照合。 -/
def dgOdotMilnorRightAxisComparisonBaseValueEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (dgKInputStableValue R (dgOdotMilnorRightAxisComparisonBaseInput R d)).obj
    (dgKInputStableValue R (dgOdotMilnorResolvedInput R d)).obj :=
  dgSmallPerfectEnvelopeValueEquivalence R (Q) ((P) ⊕ (P)) (X)

/-- 概要：同じ逆回転小基底の ν 値を同じ二実像小基底の ν 値へ戻す。
方針：元 cone・二重 shift の指定族の全包絡評価を使う。
規約：元実像を保持。使われ方：二段評価の第一段。 -/
def dgOdotMilnorRightAxisBaseStepValueEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (dgKInputStableValue R (dgOdotMilnorRightAxisIdentityBaseInput R d)).obj
    (dgKInputStableValue R (dgOdotMilnorRightAxisComparisonBaseInput R d)).obj :=
  dgSmallPerfectEnvelopeValueEquivalence R (T) ((H) ⊕ (H)) (Y)

/-- 概要：同じ逆回転基底の ν 値と元 resolved 商 ν 値の指定同値。
方針：二段の同じ包絡評価を合成する。
規約：元の商・二実像・実 cone を保持。使われ方：実右面の対角始域。 -/
def dgOdotMilnorRightAxisBaseValueEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (dgKInputStableValue R (dgOdotMilnorRightAxisIdentityBaseInput R d)).obj
    (dgKInputStableValue R (dgOdotMilnorResolvedInput R d)).obj :=
  (dgOdotMilnorRightAxisBaseStepValueEquivalence R d).trans
    (dgOdotMilnorRightAxisComparisonBaseValueEquivalence R d)

/-- 概要：同じ二段値同値は元逆回転基底の実包絡評価を全回収する。
方針：第一段の元 native 評価同型を第二段で後合成する。
規約：全関手同型を保持。使われ方：D2 基底変更の指定頂点比較。 -/
def dgOdotMilnorRightAxisBaseValueEquivalence_native : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (dgKNativeValueComparison R (U) ≫ (dgOdotMilnorRightAxisBaseValueEquivalence R d).hom)
    (((dgSmallPerfectEnvelopeNerveEquivalence R (T) ((H) ⊕ (H)) (Y)).hom ≫
      (dgKNativePerfectValueEquivalence R (T)).hom) ≫
      (dgOdotMilnorRightAxisComparisonBaseValueEquivalence R d).hom) :=
  dgSmallPerfectEnvelopeValueEquivalence_native_postcomp R (T) ((H) ⊕ (H)) (Y)
    (dgOdotMilnorRightAxisComparisonBaseValueEquivalence R d).hom

/-- 概要：同じ実差終域の ν 値を同じ resolved 商値へ戻す指定同値。
方針：実 cone 全像評価と同じ二段包絡評価を合成する。
規約：元の実差を変更しない。使われ方：実右面の商終域。 -/
def dgOdotMilnorRightAxisDifferenceResolvedValueEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (dgKInputStableValue R (dgOdotMilnorRightAxisIdentityDifferenceInput R d)).obj
    (dgKInputStableValue R (dgOdotMilnorResolvedInput R d)).obj :=
  (dgOdotMilnorRightAxisIdentityDifferenceValueEquivalence R d).trans
    (dgOdotMilnorRightAxisBaseValueEquivalence R d)

/-- 概要：同じ第一成分の固定 ν 辺は元 graph Perf 延長を全回収する。
方針：元の指定二像への厳密持ち上げに同じ ν 比較を適用する。
規約：元関手の全 Hom 作用を保持。使われ方：中央比較の第一境界。 -/
def dgOdotMilnorRightAxisSourceComponentNuComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (dgKNativeValueComparison R (P) ≫
      (dgKNativeInputExactMap R (P) (T) (dgPerfectComparisonFirst R (Q) (F) (G))).hom ≫
      (dgOdotMilnorRightAxisComparisonBaseValueEquivalence R d).hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (F) ≫ (dgKNativePerfectValueEquivalence R (Q)).hom) :=
  dgSmallPerfectEnvelopeLiftNuComparison R (Q) ((P) ⊕ (P)) (X) (P) (F) Sum.inl
    (fun _ => rfl)

/-- 概要：同じ第二成分の固定 ν 辺は元恒等 graph Perf 延長を全回収する。
方針：元の指定二像への厳密持ち上げに同じ ν 比較を適用する。
規約：元関手を共役で置換しない。使われ方：中央比較の第二境界。 -/
def dgOdotMilnorRightAxisTargetComponentNuComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (dgKNativeValueComparison R (P) ≫
      (dgKNativeInputExactMap R (P) (T) (dgPerfectComparisonSecond R (Q) (F) (G))).hom ≫
      (dgOdotMilnorRightAxisComparisonBaseValueEquivalence R d).hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (G) ≫ (dgKNativePerfectValueEquivalence R (Q)).hom) :=
  dgSmallPerfectEnvelopeLiftNuComparison R (Q) ((P) ⊕ (P)) (X) (P) (G) Sum.inr
    (fun _ => rfl)

end SerrePositivity.KST.SConstruction
