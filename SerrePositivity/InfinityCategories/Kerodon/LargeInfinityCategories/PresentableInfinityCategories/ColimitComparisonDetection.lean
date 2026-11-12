module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HomotopyColimitValueDetection
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationNaturality
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
概要：余極限を保つ二関手の指定比較の可逆性を生成図式から検出する。
方針：同じ比較のホモトピー代表へ余極限頂点の可逆性判定を適用する。
規約：比較射自身を固定し、頂点同型にも自然性で移す。
使われ方：filtered と幾何学的実現で生成された P_Σ の保存判定。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：同型な二頂点で指定比較成分の可逆性は同値。
方針：同じ h 圏自然変換の同型に関する自然性を使う。
規約：比較成分を選び直さない。
使われ方：生成表示の頂点同型に沿う検出。 -/
lemma functorHomEvaluate_isIso_iff_vertexIso
    {X Y : SSet.{u}} [Quasicategory Y] {F G : X ⟶ Y}
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G) {x y : X _⦋0⦌} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate η x) ↔ IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate η y) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorCellToNatTrans_app_eq_evaluate] using
    NatTrans.isIso_app_iff_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.functorCellToNatTrans η) e

/-- 概要：指定比較が図式上で可逆なら保存された余極限頂点でも可逆。
方針：同じ射のホモトピー代表に既存の余極限可逆性検出を適用する。
規約：元の全余錐と指定比較を保持する。
使われ方：二段階の生成に沿う同型検出。 -/
lemma functorHomEvaluate_isIso_of_colimit
    {K X Y : SSet.{u}} [Quasicategory Y] {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) {F G : X ⟶ Y}
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F c))
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone G c)) (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G)
    (hη : ∀ j, IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate η (p.app (Opposite.op ⦋0⦌) j))) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate η c.vertex) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.homotopy_colimit_value_isInvertible c hF hG
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy η) (fun j ↦ ?_)
  · change IsIso (SSet.Truncated.HomotopyCategory.homMk _) at h
    rwa [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_component] at h
  · change IsIso (SSet.Truncated.HomotopyCategory.homMk _)
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_component]
    exact hη j

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
