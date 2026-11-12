module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridLowerRectangleCocone
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridExtension

/-!
概要：実左 Kan の局所余極限から格子の最初の右面の押し出し性を得る。
方針：元の射影・実余錐・全単体の頂点式を保持して比較する。
規約：一般安定性の結論は先取りしない。使われ方：HA 1.4.2.15 の比較格子。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
variable {P : Type u} [PartialOrder P]

lemma excisionGridLowerRectangle_right_pushout {X : SSet.{u}} [Quasicategory X]
    (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} ⟶ X)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone (nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSeedInclusion)
      F (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint 2 1)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridLowerRectangle ≫ F) 0) := by
  have hl := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isColimit_posetSubtypeLowerCocone_of_canonical _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridSeed
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint 2 1) F h
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridLowerRectangleCocone) := by
    apply (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isColimitCone_iff_of_val_eq _ _ ?_).mpr hl
    exact congrArg (fun f ↦ f ≫ F) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridLowerRectangleCocone_val
  have hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridLowerRectangleCocone).val =
      ((_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.pastingCocone (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridLowerRectangle ≫ F)).restrict
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridLowerSeedCornerIso.hom).val := by
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridLowerRectangleCocone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.restrict,
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.pastingCocone, Category.assoc]
  have hd := (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isColimitCone_iff_of_val_eq _ _ hv).mp hc
  exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.pastingCocone_isColimitCone_iff_right _).mp
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_restrict_of_isIso _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridLowerSeedCornerIso.hom).mpr hd)

lemma ExcisionGridExtension.lower_right_pushout {X : SSet.{u}} [Quasicategory X]
    {G : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSeedIndex.{u} ⟶ X} {z : X _⦋0⦌}
    (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridExtension G z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridLowerRectangle ≫ d.core) 0) :=
  excisionGridLowerRectangle_right_pushout d.core
    (d.core_colimit (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint 2 1)))

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
