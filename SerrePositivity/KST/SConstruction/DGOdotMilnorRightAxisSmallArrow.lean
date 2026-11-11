module
public import SerrePositivity.KST.SConstruction.DGPerfectComparisonStrictArrow
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeArrow
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisBaseValue
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisPerfNativeNaturality

/-!
概要：元 resolved graph 比較の同じ実 Perf 延長射を、二実像小基底へ全体として制限する。
方針：同じ厳密変換の全 Hom 自然性を充満小模型に持ち込み、包含で元射を回収する。
規約：元比較射を共役で置換しない。使われ方：固定 ν 中央比較の小基底表示。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet DifferentialGraded InfinityCategories
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
local notation "L" => dgPerfectComparisonFirst R (Q) (F) (G)
local notation "M" => dgPerfectComparisonSecond R (Q) (F) (G)
local notation "I" => dgSmallPerfectEnvelopeInclusion R (Q) ((P) ⊕ (P)) (X)

/-- 概要：元比較の同じ実 Perf 延長を全厳密変換として保持する。
方針：元 resolved graph 比較を同じ指定商包含で延長する。
規約：元の二実関手間の変換。使われ方：小基底への制限の元射。 -/
def dgOdotMilnorRightAxisQuotientStrictNatTrans : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (F) (G) :=
  dgCellResolvedGraphPerfectExtendedStrictNatTrans.{u, u} R (B) (Q)
    (dgOdotMilnorRightAxisEndofunctor R d) (DGFunctor.id (B))
    (dgOdotMilnorRightAxisComparison R d) (dgOdotMilnorResolvedInclusion R d)

/-- 概要：同じ元比較を二実像小基底内の全厳密変換にする。
方針：同じ指定二族と元全 Hom 自然性を使用する。
規約：元閉零成分を保持。使われ方：小基底の元比較射。 -/
def dgOdotMilnorRightAxisSmallStrictNatTrans : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (L) (M) :=
  dgSmallPerfectEnvelopeStrictNatTrans R (Q) ((P) ⊕ (P)) (X) (P) (F) (G)
    Sum.inl Sum.inr (fun _ => rfl) (fun _ => rfl)
    (dgOdotMilnorRightAxisQuotientStrictNatTrans R d)

/-- 概要：同じ小基底比較の元全 native 射。
方針：同じ厳密変換を元 nerve の全射作用で写す。
規約：元二成分・元比較を保持。使われ方：全包絡評価の自然性。 -/
def dgOdotMilnorRightAxisSmallNerveArrow :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (L)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (M)) :=
  dgSmallPerfectEnvelopeNerveArrow R (Q) ((P) ⊕ (P)) (X) (P) (F) (G)
    Sum.inl Sum.inr (fun _ => rfl) (fun _ => rfl)
    (dgOdotMilnorRightAxisQuotientStrictNatTrans R d)

/-- 概要：同じ小基底全 native 射の包含像は元の実 Perf 比較射。
方針：元全厳密変換を保持する包含回収を特殊化する。
規約：頂点成分だけでは代用しない。使われ方：元中央比較射との同一性。 -/
lemma dgOdotMilnorRightAxisSmallNerveArrow_inclusion :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (L)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (M)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I))
      (dgOdotMilnorRightAxisSmallNerveArrow R d))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R (P) (PerfectDGModule R (Q))
        (dgOdotMilnorRightAxisQuotientStrictNatTrans R d)) :=
  dgSmallPerfectEnvelopeNerveArrow_inclusion R (Q) ((P) ⊕ (P)) (X) (P) (F) (G)
    Sum.inl Sum.inr (fun _ => rfl) (fun _ => rfl)
    (dgOdotMilnorRightAxisQuotientStrictNatTrans R d)

/-- 概要：元実 Perf 比較射の全加群包含像は保存済み native 全比較射。
方針：同じ二段後合成と元 nerve 後合成整合性を使う。
規約：元射を選び直さない。使われ方：既存 native 増大 square との接続。 -/
lemma dgOdotMilnorRightAxisQuotientStrictNatTrans_raw :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (G))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGModuleInclusion R (Q) Set.univ))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R (P) (PerfectDGModule R (Q))
        (dgOdotMilnorRightAxisQuotientStrictNatTrans R d)))
      (dgOdotMilnorRightAxisPerfNativeArrow R d) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_postcomp_heq R (P) (PerfectDGModule R (Q))
    (RightModule R (Q)) (dgOdotMilnorRightAxisQuotientStrictNatTrans R d)
    (perfectDGModuleInclusion R (Q) Set.univ)).symm

/-- 概要：同じ元比較射の固定 ν 評価は元の二成分比較を保って自然。
方針：包絡値の全比較の自然性を同じ小基底全射へ特殊化する。
規約：元射を共役で置換しない。使われ方：元 native square から固定 ν への接続。 -/
lemma dgOdotMilnorRightAxisSmallNerveArrow_value_naturality :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (L)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (M))
      (dgKNativeValueComparison R (T) ≫
        (dgOdotMilnorRightAxisComparisonBaseValueEquivalence R d).hom)
      (dgOdotMilnorRightAxisSmallNerveArrow R d) ≫
      ((dgSmallPerfectEnvelopeValueEquivalence_native R (Q) ((P) ⊕ (P)) (X)).precomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (M))).hom =
    ((dgSmallPerfectEnvelopeValueEquivalence_native R (Q) ((P) ⊕ (P)) (X)).precomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (L))).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (L)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (M))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I) ≫ (dgKNativePerfectValueEquivalence R (Q)).hom)
        (dgOdotMilnorRightAxisSmallNerveArrow R d) :=
  dgSmallPerfectEnvelopeValueEquivalence_native_naturality R (Q) ((P) ⊕ (P)) (X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (L)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (M)) (dgOdotMilnorRightAxisSmallNerveArrow R d)

/-- 概要：同じ固定 ν 値への全射評価は元実 Perf 比較射そのものを回収する。
方針：元全変換の包含・評価回収を同じ商の固定値へ特殊化する。
規約：頂点別の比較で代用しない。使われ方：同じ中央比較射の指定 ν 像。 -/
lemma dgOdotMilnorRightAxisSmallNerveArrow_value :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (L)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (M))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I) ≫ (dgKNativePerfectValueEquivalence R (Q)).hom)
      (dgOdotMilnorRightAxisSmallNerveArrow R d))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (G))
        (dgKNativePerfectValueEquivalence R (Q)).hom
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R (P) (PerfectDGModule R (Q))
          (dgOdotMilnorRightAxisQuotientStrictNatTrans R d))) :=
  dgSmallPerfectEnvelopeNerveArrow_evaluation R (Q) ((P) ⊕ (P)) (X) (P) (F) (G)
    Sum.inl Sum.inr (fun _ => rfl) (fun _ => rfl)
    (dgOdotMilnorRightAxisQuotientStrictNatTrans R d)
    (dgKNativePerfectValueEquivalence R (Q)).hom

/-- 概要：同じ実 Perf 厳密比較の閉零成分は中央射に使った元比較そのもの。
方針：元の unit パラメータと実 Perf 延長の同じ閉元を回収する。
規約：別の同型成分へ変更しない。使われ方：実 Hom gluing 比較辺との照合。 -/
lemma dgOdotMilnorRightAxisQuotientStrictNatTrans_app (x : P) :
    ((dgOdotMilnorRightAxisQuotientStrictNatTrans R d).app x).val =
      (cycleFromUnit _ ((dgOdotMilnorRightAxisQuotientComparison R d).app x)).val := by
  rfl

/-- 概要：同じ小基底の全厳密変換は元 Hom gluing の比較閉射を保持する。
方針：元閉零成分の照合を同じ閉射・閉元対応で戻す。
規約：中央射の実比較辺を変更しない。使われ方：全 interval 比較と実中央射の接続。 -/
lemma dgOdotMilnorRightAxisSmallStrictNatTrans_comparisonMap (x : P) :
    (closedHomEquiv R (T) ((L).obj x) ((M).obj x)).symm
      ((dgOdotMilnorRightAxisSmallStrictNatTrans R d).app x) =
      dgPerfectComparisonMap R (Q) (F) (G) (dgOdotMilnorRightAxisQuotientComparison R d) x :=
  dgPerfectComparisonStrictNatTrans_comparisonMap R (Q) (P) (F) (G)
    (dgOdotMilnorRightAxisQuotientComparison R d)
    (dgOdotMilnorRightAxisQuotientStrictNatTrans R d)
    (dgOdotMilnorRightAxisQuotientStrictNatTrans_app R d) x

end SerrePositivity.KST.SConstruction
