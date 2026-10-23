module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalDiagramColimitDescent
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
概要：底上の射に沿う、同じ二図式の間の区間 Hom の制限と合成則。
方針：底上の可換式で両端を正規化し、展開した族で単位・合成を確認する。
規約：元の前合成と全パラメーターの区間族を保持する。
使われ方：分類先の Hom の降下を厳密な極限錐へ束ねる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {B X : SSet.{u}} (F G : B ⟶ X)

/-- 底上の同じ射に沿って制限し、元の底上の図式の両端へ揃える。 -/
def intervalDiagramOverPre {a b : Over B} (f : a ⟶ b) :
    intervalMappingSpace (functorVertex (b.hom ≫ F)) (functorVertex (b.hom ≫ G)) ⟶
      intervalMappingSpace (functorVertex (a.hom ≫ F)) (functorVertex (a.hom ≫ G)) :=
  intervalMappingPostOfEq ((pre f.left).app X) _ _
    (by change functorVertex (f.left ≫ (b.hom ≫ F)) = _
        rw [← Category.assoc, Over.w f])
    (by change functorVertex (f.left ≫ (b.hom ≫ G)) = _
        rw [← Category.assoc, Over.w f])

/-- 同じ底上の制限は、元の区間族の前合成として展開される。 -/
lemma intervalDiagramOverPre_uncurry {T : SSet.{u}} {a b : Over B} (f : a ⟶ b)
    (s : T ⟶ intervalMappingSpace
      (functorVertex (b.hom ≫ F)) (functorVertex (b.hom ≫ G))) :
    intervalMappingUncurry (s ≫ intervalDiagramOverPre F G f) =
      intervalMappingUncurry s ≫ (pre f.left).app X :=
  intervalMappingPostOfEq_uncurry _ _ _ _ _ s

/-- 底上の恒等射の同じ区間 Hom の制限は恒等。 -/
lemma intervalDiagramOverPre_id (a : Over B) : intervalDiagramOverPre F G (𝟙 a) = 𝟙 _ := by
  apply intervalMappingUncurry_injective
  have h := intervalDiagramOverPre_uncurry F G (𝟙 a) (𝟙 _)
  rw [Category.id_comp] at h
  rw [h]
  change _ ≫ (pre (𝟙 a.left)).app X = _
  rw [pre_id, NatTrans.id_app, Category.comp_id]

/-- 二つの底上の同じ制限は、合成した底上の射の制限に等しい。 -/
lemma intervalDiagramOverPre_comp {a b c : Over B} (f : a ⟶ b) (g : b ⟶ c) :
    intervalDiagramOverPre F G g ≫ intervalDiagramOverPre F G f =
      intervalDiagramOverPre F G (f ≫ g) := by
  apply intervalMappingUncurry_injective
  rw [intervalDiagramOverPre_uncurry]
  have hg := intervalDiagramOverPre_uncurry F G g (𝟙 _)
  have hfg := intervalDiagramOverPre_uncurry F G (f ≫ g) (𝟙 _)
  rw [Category.id_comp] at hg hfg
  rw [hg, hfg, Category.assoc]
  congr 1

/-- 大域的な区間 Hom の制限は、同じ底上の射の制限に整合する。 -/
lemma intervalDiagramOverPre_restriction {a b : Over B} (f : a ⟶ b) :
    intervalDiagramRestriction b.hom F G ≫ intervalDiagramOverPre F G f =
      intervalDiagramRestriction a.hom F G := by
  apply intervalMappingUncurry_injective
  rw [intervalDiagramOverPre_uncurry]
  have hb := intervalDiagramRestriction_uncurry b.hom F G (𝟙 _)
  have ha := intervalDiagramRestriction_uncurry a.hom F G (𝟙 _)
  rw [Category.id_comp] at hb ha
  rw [hb, ha, Category.assoc]
  congr 1
  rw [← NatTrans.comp_app, ← pre_map, Over.w f]

end SerrePositivity.InfinityCategories
