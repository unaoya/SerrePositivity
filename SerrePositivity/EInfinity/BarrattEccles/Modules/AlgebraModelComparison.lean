module

public import SerrePositivity.EInfinity.Modules.RelativeLocalizationEquivalence
public import SerrePositivity.EInfinity.BarrattEccles.AlgebraRelativeComparisons
public import SerrePositivity.EInfinity.BarrattEccles.Modules.StrictRegularSection

/-!
# 同じ BE 底の全代数・cofibrant 模型の全局所化比較

概要：HA §4.2.3 の加群族の底を、既存の同じ二模型の間で移す。
方針：元の相対関手と指定弱自然比較の全 nerve への係数移送を使う。
規約：新しい代数模型・任意 E への輸送は作らない。
使われ方：同じ全加群族と正則加群の底の模型の比較。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.EInfinity.Modules _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
variable (A : Type u) [CommRing A]

/-- 概要：同じ cofibrant 包含の局所化は全準圏同値（HA §4.2.3）。
方針：元の包含・置換と指定弱比較を全 nerve の判定に渡す。
規約：元の係数 ∞ 関手。使われ方：同じ底の模型の移送。 -/
lemma cAlgToAlgebraLocalization_isQCatEquivalence :
    IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap (cofibrantToAlgebraDKRelative A)) :=
  localizationNerveMap_isQCatEquivalence_of_weak_comparisons
    (cofibrantToAlgebraDKRelative A) (algebraToCofibrantDKRelative A)
    (cofibrantDKComparison A) (cofibrantDKComparison_weak A)
    (algebraDKComparison A) (algebraDKComparison_weak A)

/-- 概要：同じ cofibrant 置換の局所化は全準圏同値（HA §4.2.3）。
方針：元の置換・包含と指定弱比較を全 nerve の判定に渡す。
規約：元の係数 ∞ 関手。使われ方：既存 CAlg への復帰。 -/
lemma algebraLocalizationToCAlg_isQCatEquivalence :
    IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap (algebraToCofibrantDKRelative A)) :=
  localizationNerveMap_isQCatEquivalence_of_weak_comparisons
    (algebraToCofibrantDKRelative A) (cofibrantToAlgebraDKRelative A)
    (algebraDKComparison A) (algebraDKComparison_weak A)
    (cofibrantDKComparison A) (cofibrantDKComparison_weak A)

/-- 概要：正則加群の実関手の底の合成は同じ模型比較の同値（HA §4.2.3）。
方針：元の合成式と同じ二つの係数関手の同値性を使う。
規約：恒等への全関手比較の回収は別。使われ方：単位の底の模型の比較。 -/
lemma moduleUnitSection_projection_isQCatEquivalence :
    IsQCatEquivalence (moduleUnitSection A ≫ moduleTotalProjection A) := by
  rw [moduleUnitSection_projection, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap_comp]
  exact (cAlgToAlgebraLocalization_isQCatEquivalence A).comp
    (algebraLocalizationToCAlg_isQCatEquivalence A)

end SerrePositivity.EInfinity.BarrattEccles
