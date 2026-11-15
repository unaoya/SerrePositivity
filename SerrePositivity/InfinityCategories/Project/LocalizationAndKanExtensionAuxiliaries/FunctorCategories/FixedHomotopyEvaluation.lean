module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationNaturality
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.PrecompositionHomotopy

/-!
概要：部分形状で時間に定値な指定ホモトピーの成分は、元の頂点で可逆。
方針：同じホモトピーの前合成の類を端点の等式の射へ同定し、元の評価の自然性を使う。
使われ方：Kerodon §7.1（Tag 02H1）、HTT 6.2.2.6 の全錐の比較。
規約：ホモトピー全体の可逆性は仮定せず、指定した部分形状だけを使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 固定した部分形状上の指定変換は、元の像の頂点で可逆な成分を持つ。 -/
lemma functorHomEvaluate_isIso_of_fixedHomotopy {A B X : SSet.{u}}
    {U V : B ⟶ X} (H : SSet.Homotopy U V) (i : A ⟶ B)
    (hi : i ≫ U = i ≫ V)
    (hH : (i ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A (Δ[1] : SSet.{u}) ≫ (i ≫ U))
    (x : A _⦋0⦌) :
    IsIso (functorHomEvaluate (SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy H)) (i.app (Opposite.op ⦋0⦌) x)) := by
  have he := homotopyHom_eqToHom (functorHomotopyPrecomp H i) hi hH
  haveI : IsIso (SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (functorHomotopyPrecomp H i))) := by
    rw [he]
    infer_instance
  have h := functorHomEvaluate_isIso (SSet.Truncated.HomotopyCategory.homMk
    (functorEdgeOfSimplicialHomotopy (functorHomotopyPrecomp H i))) x
  rw [functorHomotopyPrecomp_hom, functorHomEvaluate_precomp] at h
  exact h

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
