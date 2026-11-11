module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalDiagramColimitDescent
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
概要：底上の射に沿う、同じ二図式の間の区間 Hom の制限と合成則。
方針：底上の可換式で両端を正規化し、展開した族で単位・合成を確認する。
規約：元の前合成と全パラメーターの区間族を保持する。
使われ方：分類先の Hom の降下を厳密な極限錐へ束ねる。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

variable {B X : SSet.{u}} (F G : B ⟶ X)

/-- 底上の同じ射に沿って制限し、元の底上の図式の両端へ揃える。 -/
def intervalDiagramOverPre {a b : Over B} (f : a ⟶ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (b.hom ≫ F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (b.hom ≫ G)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (a.hom ≫ F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (a.hom ≫ G)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq ((pre f.left).app X) _ _
    (by change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f.left ≫ (b.hom ≫ F)) = _
        rw [← Category.assoc, Over.w f])
    (by change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f.left ≫ (b.hom ≫ G)) = _
        rw [← Category.assoc, Over.w f])

/-- 同じ底上の制限は、元の区間族の前合成として展開される。 -/
lemma intervalDiagramOverPre_uncurry {T : SSet.{u}} {a b : Over B} (f : a ⟶ b)
    (s : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (b.hom ≫ F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (b.hom ≫ G))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (s ≫ intervalDiagramOverPre F G f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry s ≫ (pre f.left).app X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq_uncurry _ _ _ _ _ s

/-- 底上の恒等射の同じ区間 Hom の制限は恒等。 -/
lemma intervalDiagramOverPre_id (a : Over B) : intervalDiagramOverPre F G (𝟙 a) = 𝟙 _ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective
  have h := intervalDiagramOverPre_uncurry F G (𝟙 a) (𝟙 _)
  rw [Category.id_comp] at h
  rw [h]
  change _ ≫ (pre (𝟙 a.left)).app X = _
  rw [pre_id, NatTrans.id_app, Category.comp_id]

/-- 二つの底上の同じ制限は、合成した底上の射の制限に等しい。 -/
lemma intervalDiagramOverPre_comp {a b c : Over B} (f : a ⟶ b) (g : b ⟶ c) :
    intervalDiagramOverPre F G g ≫ intervalDiagramOverPre F G f =
      intervalDiagramOverPre F G (f ≫ g) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective
  rw [intervalDiagramOverPre_uncurry]
  have hg := intervalDiagramOverPre_uncurry F G g (𝟙 _)
  have hfg := intervalDiagramOverPre_uncurry F G (f ≫ g) (𝟙 _)
  rw [Category.id_comp] at hg hfg
  rw [hg, hfg, Category.assoc]
  congr 1

/-- 大域的な区間 Hom の制限は、同じ底上の射の制限に整合する。 -/
lemma intervalDiagramOverPre_restriction {a b : Over B} (f : a ⟶ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction b.hom F G ≫ intervalDiagramOverPre F G f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction a.hom F G := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective
  rw [intervalDiagramOverPre_uncurry]
  have hb := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction_uncurry b.hom F G (𝟙 _)
  have ha := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction_uncurry a.hom F G (𝟙 _)
  rw [Category.id_comp] at hb ha
  rw [hb, ha, Category.assoc]
  congr 1
  rw [← NatTrans.comp_app, ← pre_map, Over.w f]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
