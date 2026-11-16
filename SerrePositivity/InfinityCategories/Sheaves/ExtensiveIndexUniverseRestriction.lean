module

public import SerrePositivity.InfinityCategories.Sheaves.ExtensiveIndexRightKan
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.AsSmallWithTerminal
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeReindexRestrictions

/-!
概要：有限被覆の添字の指定全錐の比較を、係数と同じ上の宇宙へ移す。
方針：終点と AsSmall の順序交換の添字同型で、既存の指定右 Kan 条件へ戻す。
規約：HTT 4.3.2、Kerodon §7.3（Tag 02Y1）の既存構成の宇宙移送。
使われ方：S1 の元の準圏値前層の有限被覆判定。係数の宇宙は上げない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
namespace SerrePositivity.InfinityCategories.Sheaves
variable (I : Type u) [SmallCategory I] {E : SSet.{u + 1}} [Quasicategory E]

/-- 指定添字同型を戻すと、元の持ち上げた脚の包含そのものになる。 -/
lemma extensiveIndexUniverse_incl :
    (nerveAsSmallIso I).hom ≫
      nerveMap (WithTerminal.incl : AsSmall.{u + 1} I ⥤ WithTerminal (AsSmall.{u + 1} I)) ≫
        (nerveWithTerminalAsSmallIso I).inv =
      (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (WithTerminal.incl : I ⥤ WithTerminal I)) := by
  rw [← Category.assoc, ← nerveWithTerminalAsSmallIso_incl, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- 同じ元の全錐の極限性は、持ち上げた脚の包含への制限で保存・反映される。 -/
lemma extensiveIndex_ulift_restrict_isLimit_iff
    (H : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (WithTerminal I)) ⟶ E)
    (hH : IsTerminalVertex
      (H.app _ (ULift.up (nerveVertex (WithTerminal.star : WithTerminal I)))))
    (c : JoinCone H) :
    IsLimitCone c ↔ IsLimitCone (restrictJoinCone c
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (WithTerminal.incl : I ⥤ WithTerminal I)))) := by
  let e := nerveWithTerminalAsSmallIso I
  let d := c.reindexIso e.symm
  have ht : IsTerminalVertex
      ((e.inv ≫ H).app _ (nerveVertex (WithTerminal.star : WithTerminal (AsSmall.{u + 1} I)))) := by
    change IsTerminalVertex (H.app _ (e.inv.app _ (ComposableArrows.mk₀ WithTerminal.star)))
    rw [nerveWithTerminalAsSmallIso_star]
    exact hH
  have h := extensiveIndex_restrict_isLimit_iff (AsSmall.{u + 1} I) (e.inv ≫ H) ht d
  let r := restrictJoinCone d
    (nerveMap (WithTerminal.incl : AsSmall.{u + 1} I ⥤ WithTerminal (AsSmall.{u + 1} I)))
  have hv : (r.reindexIso (nerveAsSmallIso I)).val =
      (restrictJoinCone c ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (WithTerminal.incl : I ⥤ WithTerminal I)))).val := by
    change joinMap (𝟙 _) (nerveAsSmallIso I).hom ≫
      (joinMap (𝟙 _) (nerveMap (WithTerminal.incl : AsSmall.{u + 1} I ⥤ _)) ≫
        (joinMap (𝟙 _) e.inv ≫ c.val)) = _
    simp only [← Category.assoc, ← joinMap_comp, Category.id_comp]
    have hs : ((nerveAsSmallIso I).hom ≫
        nerveMap (WithTerminal.incl : AsSmall.{u + 1} I ⥤ _) ) ≫ e.inv =
        (SSet.uliftFunctor.{u + 1, u}).map
          (nerveMap (WithTerminal.incl : I ⥤ WithTerminal I)) := by
      simpa only [Category.assoc] using extensiveIndexUniverse_incl I
    rw [hs]
    rfl
  exact (isLimitCone_iff_reindexIso c e.symm).trans
    (h.trans ((isLimitCone_iff_reindexIso r (nerveAsSmallIso I)).trans
      (isLimitCone_iff_of_cone_val_eq _ _ hv)))

end SerrePositivity.InfinityCategories.Sheaves
