module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetNestedLowerCocone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.InitialBoundaryCoconeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCanonicalMapping

/-!
概要：同じ左 Kan の局所余極限を部分図式へ移し native 余錐の制限を判定する。
方針：同じ実図式の native 余錐と頂点を保持して比較する。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の中央面。

対応節は Kerodon 7.3（Tag 02Y1）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
variable {P : Type u} [PartialOrder P]

lemma posetSubtype_canonicalColimit_nested (T U : P → Prop) (hTU : ∀ p, T p → U p)
    (c : {p : P // U p}) {X : SSet.{u}} (F : nerve P ⟶ X)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion T))
      F (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c.val))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone
      (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion (fun p : {p : P // U p} ↦ T p.val)))
      (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion U) ≫ F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)) := by
  have hl := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isColimit_posetSubtypeLowerCocone_of_canonical T c.val F h
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_restrict_of_isIso _
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetNestedLowerNerveIso T U hTU c).hom).mp hl
  have hn : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion U) ≫ F)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone (fun p : {p : P // U p} ↦ T p.val) c)) := by
    apply (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isColimitCone_iff_of_val_eq _ _ ?_).mpr he
    change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone (fun p : {p : P // U p} ↦ T p.val) c).val ≫
        (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion U) ≫ F) =
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone T c.val).restrict
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetNestedLowerNerveIso T U hTU c).hom).val ≫ F
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetNestedLowerCocone_val T U hTU c]
  have hd := (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isColimitCone_iff_of_val_eq _ _
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone_postcomp_val (fun p : {p : P // U p} ↦ T p.val) c
      (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion U) ≫ F))).mp hn
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_restrict_of_isIso _
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerKanShapeIso (fun p : {p : P // U p} ↦ T p.val) c).hom).mpr hd

lemma isColimitCone_iff_restrict_of_poset_nested_canonical
    (T U : P → Prop) (hTU : ∀ p, T p → U p) {X : SSet.{u}} [Quasicategory X]
    (F : nerve P ⟶ X)
    (hF : ∀ p : (nerve P) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion T)) F p))
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion U) ≫ F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (d.restrict
      (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion (fun p : {p : P // U p} ↦ T p.val)))) := by
  let i := nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion (fun p : {p : P // U p} ↦ T p.val))
  let : Mono i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.posetSubtypeInclusion_nerveMap_mono _
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.isColimitCone_iff_restrict_of_initialBoundary i
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonical_pre_initialBoundary
  intro c
  obtain ⟨c, rfl⟩ := nerveEquiv.symm.surjective c
  exact posetSubtype_canonicalColimit_nested T U hTU c F (hF (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c.val))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
