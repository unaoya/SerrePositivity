module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FixedHomotopyEvaluation

/-!
概要：部分形状で時間に定値なホモトピーの端点は、その部分で厳密に一致する。
方針：同じ全円柱の終端で評価し、元の始端への定値性を使う。
使われ方：Kerodon §7.1（Tag 02H1）、HTT 6.2.2.6 の全錐の頂点の比較。
規約：頂点の一致を追加仮定にせず、指定した固定条件から回収する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 指定部分で時間に定値なホモトピーは、その部分の両端の全射を一致させる。 -/
lemma fixedHomotopy_endpoints {A B X : SSet.{u}} {U V : B ⟶ X}
    (H : SSet.Homotopy U V) (i : A ⟶ B)
    (hH : (i ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A (Δ[1] : SSet.{u}) ≫ (i ≫ U)) :
    i ≫ U = i ≫ V := by
  calc
    i ≫ U = SSet.ι₁ ≫ (fst A (Δ[1] : SSet.{u}) ≫ (i ≫ U)) := by
      rw [← Category.assoc, SSet.ι₁_fst, Category.id_comp]
    _ = SSet.ι₁ ≫ ((i ▷ (Δ[1] : SSet.{u})) ≫ H.h) := by rw [hH]
    _ = i ≫ V := by rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, H.h₁]

/-- 固定した全円柱だけを入力にすれば、同じ元の頂点成分が可逆である。 -/
lemma functorHomEvaluate_isIso_of_fixedHomotopy_only {A B X : SSet.{u}}
    {U V : B ⟶ X} (H : SSet.Homotopy U V) (i : A ⟶ B)
    (hH : (i ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A (Δ[1] : SSet.{u}) ≫ (i ≫ U))
    (x : A _⦋0⦌) :
    IsIso (functorHomEvaluate (SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy H)) (i.app (Opposite.op ⦋0⦌) x)) :=
  functorHomEvaluate_isIso_of_fixedHomotopy H i (fixedHomotopy_endpoints H i hH) hH x

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
