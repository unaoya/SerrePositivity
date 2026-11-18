module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.NerveConeWhiskerPostcompose
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RightKanLimitCompositionArbitrary

/-!
概要：元の通常の三角形の指定右 Kan 条件は、任意の準圏係数で元の全錐の極限性を比較する。
方針：同じ通常の全ホモトピーの始端だけを制限錐へ揃え、全表現可能関手での比較へ接続する。
使われ方：Kerodon §7.3（Tag 02Y1）、HTT 6.2.2.6 の篩の二段分解と交叉降下。
規約：係数に極限存在を仮定しない。元の指定三角形と全錐を保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
variable {I J C : Type u} [Category.{u} I] [Category.{u} J] [Category.{u} C]

/-- 元の三角形の同じ円柱を、nerve の前合成による指定余単位として使う。 -/
def nerveWhiskerCoefficientCounitHomotopy (δ : I ⥤ J) {P : J ⥤ C} {Q : I ⥤ C}
    (η : δ ⋙ P ⟶ Q) {X : SSet.{u}} (U : nerve C ⟶ X) :
    SSet.Homotopy (nerveMap δ ≫ (nerveMap P ≫ U)) (nerveMap Q ≫ U) where
  h := (functorHomotopyPostcomp (nerveNatTransHomotopy η) U).h
  h₀ := (functorHomotopyPostcomp (nerveNatTransHomotopy η) U).h₀.trans
    (nerveWhiskerCoefficient_eq δ P U)
  h₁ := (functorHomotopyPostcomp (nerveNatTransHomotopy η) U).h₁
  rel := (functorHomotopyPostcomp (nerveNatTransHomotopy η) U).rel

/-- 元の通常の全錐の同じ変換を、実際の制限錐から始まる指定ホモトピーへ揃える。 -/
def nerveConeWhiskerPostcomposeHomotopy (δ : I ⥤ J) {P : J ⥤ C} {Q : I ⥤ C}
    (c : Cone P) (η : δ ⋙ P ⟶ Q) {X : SSet.{u}} (U : nerve C ⟶ X) :
    SSet.Homotopy (restrictJoinCone (mapJoinCone U (nerveCone c)) (nerveMap δ)).val
      (mapJoinCone U (nerveCone ((Cone.postcompose η).obj (c.whisker δ)))).val where
  h := (functorHomotopyPostcomp (nerveConePostcomposeHomotopy (c.whisker δ) η) U).h
  h₀ := (functorHomotopyPostcomp (nerveConePostcomposeHomotopy (c.whisker δ) η) U).h₀.trans
    (nerveConeWhiskerPostcompose_val δ c U)
  h₁ := (functorHomotopyPostcomp (nerveConePostcomposeHomotopy (c.whisker δ) η) U).h₁
  rel := (functorHomotopyPostcomp (nerveConePostcomposeHomotopy (c.whisker δ) η) U).rel

/-- 元の指定三角形が右 Kan 条件を満たせば、任意の準圏値で同じ両錐の極限性は同値。 -/
lemma nerveConeWhiskerPostcompose_isLimit_iff_arbitrary (δ : I ⥤ J)
    {P : J ⥤ C} {Q : I ⥤ C} (c : Cone P) (η : δ ⋙ P ⟶ Q)
    {X : SSet.{u}} [Quasicategory X] (U : nerve C ⟶ X)
    (hη : IsRightKanExtension (nerveMap δ) (nerveMap Q ≫ U) (nerveMap P ≫ U)
      (nerveWhiskerCoefficientCounitHomotopy δ η U)) :
    IsLimitCone (mapJoinCone U (nerveCone c)) ↔
      IsLimitCone (mapJoinCone U (nerveCone ((Cone.postcompose η).obj (c.whisker δ)))) := by
  refine isLimitCone_iff_of_rightKan_comparison (nerveMap δ)
    (mapJoinCone U (nerveCone c))
    (mapJoinCone U (nerveCone ((Cone.postcompose η).obj (c.whisker δ))))
    (nerveWhiskerCoefficientCounitHomotopy δ η U) hη
    (nerveConeWhiskerPostcomposeHomotopy δ c η U) ?_ ?_
  · change (joinInr (Δ[0] : SSet.{u}) (nerve I) ▷ (Δ[1] : SSet.{u})) ≫
      (nerveConePostcomposeHomotopy (c.whisker δ) η).h ≫ U =
      (nerveNatTransHomotopy η).h ≫ U
    rw [← Category.assoc, nerveConePostcomposeHomotopy_diagram]
  · change (joinInl (Δ[0] : SSet.{u}) (nerve I) ▷ (Δ[1] : SSet.{u})) ≫
      (nerveConePostcomposeHomotopy (c.whisker δ) η).h ≫ U = _
    rw [← Category.assoc, nerveConePostcomposeHomotopy_fixedVertex,
      ← nerveConeWhiskerPostcompose_val δ c U]
    simp only [mapJoinCone, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
