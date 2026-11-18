module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinRightHom
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluation

/-!
概要：全関手の端点の等式で輸送しても、元の頂点成分の可逆性は変わらない。
方針：二つの端点の等式を消去し、同じ評価へ戻す。
使われ方：Kerodon §7.3（Tag 02Y1）、HTT 6.2.2.6 の全錐の制限の比較。
規約：変換全体の可逆性は要求しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 元の同じ頂点における成分の可逆性は、全関手の端点の等式による表示変更に不変。 -/
lemma kanFunctorHomCongr_evaluate_isIso_iff {A X : SSet.{u}} {U V U' V' : A ⟶ X}
    (hU : U = U') (hV : V = V') (α : FunctorHom U V) (x : A _⦋0⦌) :
    IsIso (functorHomEvaluate (kanFunctorHomCongr hU hV α) x) ↔
      IsIso (functorHomEvaluate α x) := by
  cases hU
  cases hV
  simp only [kanFunctorHomCongr, Iso.homCongr_apply, eqToIso.inv, eqToIso.hom,
    eqToHom_refl, Category.id_comp, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
