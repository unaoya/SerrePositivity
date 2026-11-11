module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCenterCocone

/-!
概要：native 左 Kan 局所余極限から比較格子の中央面の押し出し性を得る。
方針：同じ実図式の native 余錐と頂点を保持して比較する。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の中央面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
variable {P : Type u} [PartialOrder P]

lemma ExcisionGridExtension.center_pushout {X : SSet.{u}} [Quasicategory X]
    {G : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSeedIndex.{u} ⟶ X} {z : X _⦋0⦌}
    (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridExtension G z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCenterSquare ≫ d.core) := by
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_restrict_of_isIso _
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCenterSpanShapeIso.hom).mp d.center_span_colimit
  apply (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isColimitCone_iff_of_val_eq _ _ ?_).mpr he
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCenterSquare) ≫ d.core =
    ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridPastCocone.restrict _).restrict _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCenterSpanShapeIso.hom).val ≫
      d.core
  exact congrArg (fun f ↦ f ≫ d.core) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCenterCocone_val.symm

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
