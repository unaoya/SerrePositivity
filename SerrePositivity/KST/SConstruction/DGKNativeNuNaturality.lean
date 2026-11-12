module
public import SerrePositivity.KST.SConstruction.DGKNativeMapComparison
public import SerrePositivity.KST.SConstruction.DGKNativeYonedaNaturality

/-!
概要：元 native dg 関手と同じ固定 ν 辺の四角形を全関手同型で比較する。
方針：同じ Perf 評価の後で Yoneda 自然性を使い、指定終域同値で反映する。
規約：元の入力写像・native 比較・固定 ν 作用を変更しない。
使われ方：実零化面の native 列を同じ固定 ν の二辺へ照合する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
variable (R : Type u) [CommRing R] (D E : Type (u + 1))
  [DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D]
  [DGCategory R E] [Small.{u} E] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R E]

omit [DGCategory R E] [Small.{u} E] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R E] in
/-- 概要：同じ native 比較は指定評価の後で元の Yoneda を回収する。
方針：終域同値の同じ単位二胞体と厳密な宇宙回収式を使用する。
規約：比較を選び直さない。使われ方：二辺自然性の指定評価での照合。 -/
def dgKNativeValueEvaluationComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (dgKNativeValueComparison R D ≫ (dgKNativePerfectValueEquivalence R D).inv)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R D)) := by
  rw [dgKNativeValueComparison_eq]
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso, Category.assoc, Category.comp_id] using
    (dgKNativePerfectValueEquivalence R D).homInvIso.precomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R D))

/-- 概要：始域の指定評価と元延長を、元関手後の Yoneda へ比較する。
方針：元の評価回収と全 Hom の Yoneda 自然性を合成する。
規約：全関手同型を保持する。使われ方：二辺比較の評価中間面。 -/
def dgKNativeNuYonedaEvaluationComparison (F : DGFunctor R D E) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (dgKNativeValueComparison R D ≫ ((dgKNativePerfectValueEquivalence R D).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R D E F)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R E)) := by
  have a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (dgKNativeValueComparison R D ≫ ((dgKNativePerfectValueEquivalence R D).inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R D E F)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R D) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R D E F)) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso, Category.assoc] using
      (dgKNativeValueEvaluationComparison R D).postcomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R D E F))
  exact a.trans (dgKNativeYonedaExtensionComparison R D E F)

/-- 概要：同じ native 二辺と固定 ν 二辺の全比較を指定終域評価の後で構成する。
方針：実評価自然性を元の Yoneda 自然性と合成する。
規約：元の評価同値を保持する。使われ方：全比較の充満忠実反映。 -/
def dgKNativeNuEvaluatedComparison (F : DGFunctor R D E) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgKNativeValueComparison R D ≫ (dgKNativeInputExactMap R D E F).hom) ≫
      (dgKNativePerfectValueEquivalence R E).inv)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F ≫ dgKNativeValueComparison R E) ≫
      (dgKNativePerfectValueEquivalence R E).inv) := by
  have a := (dgKNativeInputMapEvaluationComparison R D E F).precomp
    (dgKNativeValueComparison R D)
  have b := dgKNativeNuYonedaEvaluationComparison R D E F
  have c := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (dgKNativeValueEvaluationComparison R E).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F)
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso, Category.assoc] using a.trans (b.trans c)

/-- 概要：同じ native 関手と固定 ν 辺は実 Yoneda 比較に関して全自然に可換。
方針：実評価自然性・元の Yoneda 自然性を指定同値で戻す。
規約：h 圏だけの射の等号に弱めない。使われ方：d④ の二辺の指定比較。 -/
def dgKNativeNuNaturality (F : DGFunctor R D E) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (dgKNativeValueComparison R D ≫ (dgKNativeInputExactMap R D E F).hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F ≫ dgKNativeValueComparison R E) :=
  (dgKNativePerfectValueEquivalence R E).symm.isQCatEquivalence.isFullyFaithful.preimageFunctorIso
    (dgKNativeNuEvaluatedComparison R D E F)

end SerrePositivity.KST.SConstruction
