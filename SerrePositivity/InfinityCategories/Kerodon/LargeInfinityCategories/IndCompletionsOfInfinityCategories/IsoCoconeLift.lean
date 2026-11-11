module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.DiagramCommaRestrictionIso

/-!
概要：同型への後合成で指定された元の全余錐を厳密に持ち上げる。
方針：指定余錐を逆射で後合成し、境界と像を同型の恒等式で回収する。
規約：指定余錐自身の等号を結論にする。
使われ方：有限半順序の固定下方部分が全体である場合の帰納基底。

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
/-- 概要：同型による元の指定余錐は厳密に持ち上がる。
方針：逆射との合成。規約：全余錐の等号。使われ方：指定下方部分の帰納基底。 -/
lemma exists_cocone_lift_of_isIso {T X Y : SSet.{u}} (F : X ⟶ Y) [IsIso F]
    (q : T ⟶ X) (G : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (q ≫ F)) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F c = G := by
  let c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q := ⟨G.val ≫ inv F, by
    rw [← Category.assoc, G.property, Category.assoc, IsIso.hom_inv_id, Category.comp_id]⟩
  refine ⟨c, Subtype.ext ?_⟩
  change (G.val ≫ inv F) ≫ F = G.val
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- 概要：同型の形状制限に沿い指定全余錐を厳密に持ち上げる。
方針：元の制限の可逆性。規約：元の q と指定像。使われ方：全下方部分の場合。 -/
lemma exists_diagramComma_cocone_lift_of_shape_isIso (κ : Cardinal.{u})
    {J K C : SSet.{u}} [Quasicategory C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)
    (f : J ⟶ K) [IsIso f] {T : SSet.{u + 1}} (q : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramComma κ D)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D f)) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D f) c = G := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction_isIso κ D f
  exact exists_cocone_lift_of_isIso _ q G

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
