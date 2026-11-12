module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridFinalCocone

/-!
概要：native 局所余極限から最終 (3,3) 面の実押し出し性を得る。
方針：同じ実図式の native 余錐・頂点・二辺を保持して比較する。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の外側の面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

lemma ExcisionGridExtension.final_pushout {X : SSet.{u}} [Quasicategory X]
    {G : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSeedIndex.{u} ⟶ X} {z : X _⦋0⦌}
    (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridExtension G z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridFinalSquare ≫ d.full) := by
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_restrict_of_isIso _
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridFinalSpanShapeIso.hom).mp d.final_span_colimit
  apply (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isColimitCone_iff_of_val_eq _ _ ?_).mpr he
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridFinalSquare) ≫ d.full =
    ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridFullPastCocone.restrict
      _).restrict _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridFinalSpanShapeIso.hom).val ≫ d.full
  exact congrArg (fun f ↦ f ≫ d.full) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridFinalCocone_val.symm

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
