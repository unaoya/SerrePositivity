module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.ConeDerivedEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.SphereClosureInput
public import SerrePositivity.KST.NonConnective.DGKappaSwindleInfinity

/-!
概要：B1 の新 sphere-only cone と実導来圏の κ-compact 部分との比較同値を公開する。
方針：新 I の既証明の全フィールドを、固定 cone の一般比較へ渡す。
規約：Ind 比較や入力全体の懸垂作用を仮定しない。
使われ方：対象別の Ind_ω／compact 接続、既存の可算和・swindle の流用。

`countableClosed` は新 I の同じ実可算直和に対する閉性である。
可算和関手と swindle はその新 I へそのまま特殊化でき、代表を取り直さない。
ここでは一般の安定 ∞ 圏を動かす swindle 族や K の消滅は主張しない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect
open CategoryTheory DifferentialGraded SSet KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  (κ : Cardinal.{u}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)

/-- 新 I に固定した、元の導来圏の κ-compact 部分への全単体比較。 -/
def dgKappaSphereClosureCompactComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGKappaCone R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R D κ hκ)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{u, max (u + 1) v} κ
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeCompactComparison R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R D κ hκ)

lemma dgKappaSphereClosureCompactComparison_inclusion :
    dgKappaSphereClosureCompactComparison R D κ hκ ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion.{u, max (u + 1) v} κ
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) =
      dgKappaConeDerivedComparison R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R D κ hκ) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeCompactComparison_inclusion R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R D κ hκ)

/-- 新 I の covers・全写像空間比較による、対象別の実比較同値。 -/
def dgKappaSphereClosureCompactEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGKappaCone R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R D κ hκ)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{u, max (u + 1) v} κ
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeCompactEquivalence R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R D κ hκ)

lemma dgKappaSphereClosureCompactEquivalence_hom :
    (dgKappaSphereClosureCompactEquivalence R D κ hκ).hom =
      dgKappaSphereClosureCompactComparison R D κ hκ := rfl

/-- 新模型でも元の可算和関手をそのまま使え、元の nerve 上で完全である。 -/
lemma dgKappaSphereClosureCountableSum_isExactFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (dgKappaConeCountableSum R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R D κ hκ))) :=
  dgKappaConeCountableSum_isExactFunctor R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R D κ hκ)

/-- 新模型の同じ実 swindle 関手と可算和関手との、既存の全関手比較。 -/
def dgKappaSphereClosureSwindleInfinityIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaSwindleSource R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R D κ hκ)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaConeCountableSum R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R D κ hκ))) :=
  dgKappaSwindleInfinityIso R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R D κ hκ)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect
