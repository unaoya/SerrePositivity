module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.PosetNestedCanonicalRestriction
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetNestedBoundCocone

/-!
概要：同じ上界への部分図式の実余錐に局所余極限を移す。
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

lemma isColimit_mapJoinCocone_of_poset_nested_canonical_bound
    (T U : P → Prop) (hTU : ∀ p, T p → U p) (c : P)
    (hbound : ∀ p, T p → p ≤ c)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion U))) (hd : d.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)
    {X : SSet.{u}} [Quasicategory X] (F : nerve P ⟶ X)
    (hF : ∀ p : (nerve P) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion T)) F p)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F d) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.isColimitCone_iff_restrict_of_poset_nested_canonical T U hTU F hF
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F d)).mpr
  have hl := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isColimit_posetSubtypeLowerCocone_of_canonical T c F (hF (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_restrict_of_isIso _
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetNestedBoundLowerNerveIso T U hTU c hbound).hom).mp hl
  apply (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isColimitCone_iff_of_val_eq _ _ ?_).mpr he
  have hv := congrArg (fun f ↦ f ≫ F)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetNestedBoundCocone_restrict_val T U hTU c hbound d hd)
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.restrict, Category.assoc] using hv

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
