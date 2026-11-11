module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FilteredPointwiseWeakEquivalences
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
概要：filtered 余極限を保つ二関手間の元の自然変換の弱同値性を、同じ余極限へ移す。
方針：元の標準余極限比較との可換式と、filtered な点ごとの弱同値保存を使う。
規約：保存性は明示的な証明引数。使われ方：WithInitial の元の錐の比較射への直接適用。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {C : Type v} [Category.{w} C] {J : Type u} [SmallCategory J]
  {F G : C ⥤ SSet.{u}} (α : F ⟶ G) (D : J ⥤ C) [Limits.HasColimit D]

/-- 元の自然変換と元の標準余極限比較は、同じ余極限脚で可換。 -/
lemma colimitPost_naturality :
    colim.map (Functor.whiskerLeft D α) ≫ colimit.post D G =
      colimit.post D F ≫ α.app (colimit D) := by
  apply colimit.hom_ext
  intro j
  simp only [colimit.ι_map_assoc, colimit.ι_post, colimit.ι_post_assoc,
    Functor.whiskerLeft_app]
  exact (α.naturality (colimit.ι D j)).symm

/-- 各段階で弱同値である元の比較は、両関手が保つ filtered 余極限でも弱同値。 -/
lemma comparison_colimit_isWeakHomotopyEquivalence [IsFiltered J]
    (hF : PreservesColimitsOfShape J F) (hG : PreservesColimitsOfShape J G)
    (hα : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (α.app (D.obj j))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (α.app (colimit D)) := by
  have := hF
  have := hG
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.filteredColimitMap_isWeakHomotopyEquivalence_of_pointwise
    (Functor.whiskerLeft D α) hα).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (asIso (colimit.post D G))).isWeakHomotopyEquivalence
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
    (colim.map (Functor.whiskerLeft D α) ≫ colimit.post D G) at h
  rw [colimitPost_naturality] at h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (asIso (colimit.post D F))).isWeakHomotopyEquivalence.cancel_left h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
