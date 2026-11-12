module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.PosetSubsetCoconeLifts
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.PosetMaximalConePushout
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.DiagramCommaConePushoutRelativeLift

/-!
概要：固定順序部分の外の極大点を追加しても、元の指定全余錐の厳密持ち上げを保つ。
方針：点除去前後の固定部分の順序同型と、元の下方余錐 pushout を接続する。
規約：元の全図式・試験族・固定部分の指定余錐を保持する。
使われ方：下方閉部分を固定する有限半順序帰納の段階。

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
/-- 概要：固定部分の外の極大点追加は指定余錐持ち上げを保つ。
方針：順序同型による二段制限と元の余錐 pushout 拡張。
規約：元の指定全余錐。使われ方：有限濃度帰納の段階。 -/
lemma hasPosetSubsetCoconeLifts_of_point_removal (κ : Cardinal.{u}) [Fact κ.IsRegular]
    {C : SSet.{u}} [Quasicategory C] {P : Type u} [PartialOrder P] [Finite P]
    (U : Set P) (a : P) (ha : a ∉ U) (hmax : IsMax a)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPosetSubsetCoconeLifts κ C {p : P // p ≠ a} (Subtype.val ⁻¹' U)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPosetSubsetCoconeLifts κ C P U := by
  intro D A hA q
  let r := nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion (fun p : P ↦ p ≠ a))
  let t := nerveMap (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.posetSubsetPointRemovalLift U a ha).toFunctor
  let e := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.orderIsoNerveIso (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.posetSubsetPointRemovalOrderIso U a ha)
  let s := nerveMap
    (OrderHom.Subtype.val (fun p : {p : P // p ≠ a} ↦ p.val ∈ U)).toFunctor
  have hes : e.hom ≫ t = s := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.posetSubsetPointRemovalOrderIso_comp U a ha
  have ht : e.inv ≫ s = t := by
    rw [← hes, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hr : t ≫ r = nerveMap (OrderHom.Subtype.val U).toFunctor :=
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.posetSubsetPointRemovalLift_comp U a ha
  have hLift : ∀ G : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone ((q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D r) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ ((SSet.uliftFunctor.{u + 1, u}).map r ≫ D) t),
      ∃ c₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D r), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ ((SSet.uliftFunctor.{u + 1, u}).map r ≫ D) t) c₁ = G := by
    rw [← ht]
    intro G
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_diagramComma_cocone_lift_comp κ _ s e.inv _
      (fun c₁ ↦ h _ A hA _ c₁)
      (fun G' ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_diagramComma_cocone_lift_of_shape_isIso κ _ e.inv _ G') G
  rw [← hr]
  intro G
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_diagramComma_cocone_cone_pushout_fix_subshape κ
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.posetNerve_maximal_cone_isPushout a hmax) D t hA
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_of_finite (Fact.out : κ.IsRegular).aleph0_le _) q hLift G

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
