module

public import SerrePositivity.KST.Spectra.PointedWeightedEndPreMap
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedRestriction

/-!
概要：点つき end と基礎単体集合の end の比較の重みへの自然性。
方針：各 end 射影で自由基点からの Hom の制限と前合成の可換式を使う。
規約：通常の end の同型の比較であり Kan 条件は不要。
使われ方：Goerss–Jardine VIII §1、HA §1.4.2。cochain の忘却と通常の Tot の比較。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed SSet

open scoped MonoidalClosed

namespace SerrePositivity.KST.Spectra.PointedWeightedEnd

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance underlyingWeightPointedEnrichment :
    EnrichedOrdinaryCategory PointedSimplicialSet.{u} PointedSimplicialSet.{u} :=
  enrichedOrdinaryCategorySelf PointedSimplicialSet.{u}

/-- 概要：点つき end の忘却の比較は重みの前合成と可換。
方針：各成分を自由基点を加える前の成分へ制限して比較する。
規約：重みの射は反変に働く。
使われ方：Goerss–Jardine VIII §1。余単体 cochain の基礎図式の比較。 -/
lemma underlyingIso_preMap {I : Type u} [SmallCategory I] {W V : I ⥤ SSet.{u}}
    (θ : W ⟶ V) (D : I ⥤ PointedSimplicialSet.{u}) :
    (preMap θ D).right ≫ (underlyingIso W D).hom =
      (underlyingIso V D).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre θ (D ⋙ PointedSimplicialSet.forget) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
  intro i
  rw [Category.assoc, underlyingIso_π, ← Category.assoc]
  have hp := congrArg Under.Hom.right (preMap_π θ D i)
  rw [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hp
  change (preMap θ D).right ≫ (end_.π (diagram W D) i).right =
    (end_.π (diagram V D) i).right ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedObject.adjoinFunctor.map (θ.app i)) (D.obj i)).right
    at hp
  rw [hp, Category.assoc, FreePointedHomRestriction.natural_pre]
  conv_rhs => rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_π, ← Category.assoc, underlyingIso_π]
  rfl

end

end SerrePositivity.KST.Spectra.PointedWeightedEnd
