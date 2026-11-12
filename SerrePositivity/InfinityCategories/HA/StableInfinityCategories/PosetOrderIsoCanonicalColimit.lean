module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetOrderIsoLowerCocone

/-!
概要：順序同型に沿って native 左 Kan の局所余極限を移す。
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

lemma posetSubtype_canonicalColimit_orderIso (e : P ≃o Q) (T : Q → Prop) (c : P)
    {X : SSet.{u}} (F : nerve Q ⟶ X)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion T))
      F (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (e c)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone
      (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion (fun p ↦ T (e p))))
      (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetOrderIsoFunctor e) ≫ F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)) := by
  have hl := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isColimit_posetSubtypeLowerCocone_of_canonical T (e c) F h
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_restrict_of_isIso _ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetOrderIsoLowerNerveIso e T c).hom).mp hl
  have hn : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetOrderIsoFunctor e) ≫ F)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone (fun p ↦ T (e p)) c)) := by
    apply (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isColimitCone_iff_of_val_eq _ _ ?_).mpr he
    change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone (fun p ↦ T (e p)) c).val ≫
        (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetOrderIsoFunctor e) ≫ F) =
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone T (e c)).restrict (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetOrderIsoLowerNerveIso e T c).hom).val ≫ F
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetOrderIsoLowerCocone_val e T c]
  have hd := (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isColimitCone_iff_of_val_eq _ _
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone_postcomp_val (fun p ↦ T (e p)) c
      (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetOrderIsoFunctor e) ≫ F))).mp hn
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_restrict_of_isIso _
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerKanShapeIso (fun p ↦ T (e p)) c).hom).mpr hd

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
