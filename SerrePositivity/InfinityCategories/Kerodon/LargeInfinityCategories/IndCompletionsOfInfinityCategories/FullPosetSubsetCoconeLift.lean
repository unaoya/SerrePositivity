module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsoCoconeLift
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.FullPosetSubsetNerveIso

/-!
概要：固定順序部分が全点を含む場合、元の全図式 comma の指定余錐は厳密に持ち上がる。
方針：元の部分型包含の nerve 写像の同型性を制限へ移す。
規約：同じ試験族と指定された全余錐を保持する。
使われ方：下方閉部分を固定する有限半順序帰納の基底。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
/-- 概要：全ての点を含む部分型への制限で、元の指定余錐を厳密に持ち上げる。
方針：同型による持ち上げ。規約：元の包含。使われ方：下方部分固定帰納の基底。 -/
lemma exists_diagramComma_cocone_lift_full_posetSubset (κ : Cardinal.{u})
    {P : Type u} [PartialOrder P] (U : Set P) (hU : ∀ p, p ∈ U)
    {C : SSet.{u}} [Quasicategory C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve P) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)
    {T : SSet.{u + 1}} (q : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramComma κ D)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D
      (nerveMap (OrderHom.Subtype.val U).toFunctor))) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D (nerveMap (OrderHom.Subtype.val U).toFunctor)) c = G := by
  letI := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.fullPosetSubsetNerveMap_isIso U hU
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_diagramComma_cocone_lift_of_shape_isIso κ D _ q G

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
