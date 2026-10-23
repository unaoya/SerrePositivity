module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.KanCoconeAugmentationComparison
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.WeakHomotopyPrecomposition

/-!
概要：反転 augmentation の弱同値性から通常の Kan 余錐自体の ∞ 余極限性を得る。
方針：全 Kan 標的への前合成を反転し、元の表現可能比較の同値性へ渡す。
規約：既存の strictNativeCocone をそのまま用い、余錐の全ての脚を保持する。
使われ方：通常の filtered Kan colimit 余錐の native な普遍性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 概要：反転重みの augmentation が弱同値なら通常の Kan 余錐は ∞ 余極限。
方針：反転した前合成と Hom 同型を通して native な表現可能判定を満たす。
規約：通常の余極限性は別に仮定しない。使われ方：filtered colimit の普遍性。 -/
lemma strictNativeCocone_isColimit_of_reflectedAugmentation_weak
    {I : Type u} [SmallCategory I] {F : I ⥤ KanObject.{u}} (c : Cocone F)
    (hc : IsWeakHomotopyEquivalence (weightedColimitAugmentation
      (bousfieldKanWeight Iᵒᵖ ⋙ SSet.opFunctor) (kanObjectForget.mapCocone c))) :
    IsColimitCone (strictNativeCocone c) := by
  apply (strictNativeCocone_isColimit_iff_reflectedRepresentableComparison c).2
  intro Y
  have (i : Iᵒᵖ) : KanComplex ((simplicialHomDiagram F.op Y ⋙ SSet.opFunctor).obj i) :=
    inferInstanceAs (KanComplex (SimplicialCategory.sHom (F.obj i.unop) Y.unop).op)
  have := bousfieldKanHolim_kanComplex (simplicialHomDiagram F.op Y ⋙ SSet.opFunctor)
  have hp := pre_isSimplicialHomotopyEquivalence_of_weakHomotopyEquivalence _ hc Y.unop.obj
  have hop := oppositeKanHomotopyEquivalence hp
  rw [← kanCoconeAugmentationComparison_factor c Y.unop]
  exact hop.comp (homotopyEquivalence_of_isIso
    (kanReflectedBousfieldKanColimitUnderlyingHomIso F Y.unop).hom)

end SerrePositivity.InfinityCategories.F2
