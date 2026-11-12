module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.DiagramCommaCoconeGluing
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.DiagramCommaGluingCompatibility

/-!
概要：左局所制限で指定余錐を持ち上げられるなら、元の pushout の右指定余錐を固定できる。
方針：右余錐の共通境界を同じ図式等号で戻し、左で持ち上げて全余錐を貼る。
規約：元の q と右指定余錐を厳密に保持する。
使われ方：極大点の局所余錐部分への制限の共終性。

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
/-- 概要：左の共有部分制限の指定余錐持ち上げから、右指定余錐を元の全体へ持ち上げる。
方針：元の共有境界を戻して貼る。規約：指定余錐自身の等号。使われ方：点追加の密度。 -/
lemma exists_diagramComma_cocone_pushout_fix_right
    (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
    {J K₁ K₂ K : SSet.{u}} {i : J ⟶ K₁} {j : J ⟶ K₂}
    {r : K₁ ⟶ K} {s : K₂ ⟶ K} (h : IsPushout i j r s)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)
    {T : SSet.{u + 1}}
    (hLift : ∀ q₁ : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramComma κ ((SSet.uliftFunctor.{u + 1, u}).map r ≫ D),
      ∀ G : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (q₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ
        ((SSet.uliftFunctor.{u + 1, u}).map r ≫ D) i),
      ∃ c₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q₁, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ
        ((SSet.uliftFunctor.{u + 1, u}).map r ≫ D) i) c₁ = G)
    (q : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramComma κ D) (c₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D s)) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D s) c = c₂ := by
  let D₁ := (SSet.uliftFunctor.{u + 1, u}).map r ≫ D
  let D₂ := (SSet.uliftFunctor.{u + 1, u}).map s ≫ D
  have hD : (SSet.uliftFunctor.{u + 1, u}).map i ≫ D₁ =
      (SSet.uliftFunctor.{u + 1, u}).map j ≫ D₂ := by
    simpa only [D₁, D₂, ← Functor.map_comp, ← Category.assoc] using
      congrArg (fun a ↦ (SSet.uliftFunctor.{u + 1, u}).map a ≫ D) h.w
  let e := eqToIso (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramComma κ) hD)
  have hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D₂ j ≫ e.inv =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D₁ i := by
    calc
      _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D₂ j) ≫ e.inv :=
        (Category.assoc _ _ _).symm
      _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D (j ≫ s) ≫ e.inv :=
        congrArg (fun a ↦ a ≫ e.inv) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction_comp κ D s j)
      _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D (i ≫ r) := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction_congr κ D h.w.symm
      _ = _ := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction_comp κ D r i).symm
  let G : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone ((q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D r) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D₁ i) :=
    ⟨c₂.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D₂ j ≫ e.inv, by
      calc
        _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ c₂.val) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D₂ j ≫ e.inv) := by
          simp only [Category.assoc]
        _ = (q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D s) ≫
            (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D₂ j ≫ e.inv) :=
          congrArg (fun a ↦ a ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D₂ j ≫ e.inv)) c₂.property
        _ = _ := by simpa only [Category.assoc] using congrArg (fun a ↦ q ≫ a) hR⟩
  obtain ⟨c₁, hc₁⟩ := hLift (q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D r) G
  have hc : (c₁.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D₁ i) ≫ e.hom =
      c₂.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D₂ j := by
    calc
      _ = (c₂.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D₂ j ≫ e.inv) ≫ e.hom :=
        congrArg (fun a ↦ a ≫ e.hom) (congrArg Subtype.val hc₁)
      _ = _ := by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  obtain ⟨c, _, hc₂⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_diagramComma_cocone_gluing κ h D q c₁ c₂
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaGluing_originalFamily_compatible κ D₁ D₂ i j hD c₁.val c₂.val hc)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaGluing_prism_compatible κ D₁ D₂ i j hD c₁.val c₂.val hc)
  exact ⟨c, hc₂⟩
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
