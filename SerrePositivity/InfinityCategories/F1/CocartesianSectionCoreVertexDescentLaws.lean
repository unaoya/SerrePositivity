module

public import SerrePositivity.InfinityCategories.F1.CocartesianSectionCoreVertexDescent

/-!
概要：頂点を覆う族から回収した core の section は、元の族と全ての局所制限を厳密に保つ。
方針：core の包含で比較し、元の section の貼り合わせの等式へ戻す。
規約：core の持ち上げは、指定された元の section の族に対して一意。
使われ方：colimit に沿う section の降下から core の降下への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {T E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [InnerFibration p]
  {J : Type v} (a : Over B) (D : J → Over B) (i : ∀ j, D j ⟶ a)
  (hi : ∀ x : a.left _⦋0⦌, ∃ j y, (i j).left.app (Opposite.op ⦋0⦌) y = x)
  (g : T ⟶ kanCocartesianSections p a.hom)
  (s : ∀ j, T ⟶ (quasicategoryCore (kanCocartesianSections p (D j).hom) : SSet.{u}))
  (hs : ∀ j, g ≫ kanCocartesianSectionsPre p (i j) =
    s j ≫ (quasicategoryCore (kanCocartesianSections p (D j).hom)).ι)

/-- 回収した core の族の包含後は、指定した元の section の族。 -/
lemma cocartesianSectionCoreLift_of_vertex_cover_ι :
    cocartesianSectionCoreLift_of_vertex_cover p a D i hi g s hs ≫
      (quasicategoryCore (kanCocartesianSections p a.hom)).ι = g :=
  quasicategoryCoreLift_ι _ _

/-- 回収した core の族は、全ての元の局所的な core の族を厳密に回収する。 -/
lemma cocartesianSectionCoreLift_of_vertex_cover_fac (j : J) :
    cocartesianSectionCoreLift_of_vertex_cover p a D i hi g s hs ≫
      quasicategoryCoreMap (kanCocartesianSectionsPre p (i j)) = s j := by
  apply (cancel_mono (quasicategoryCore (kanCocartesianSections p (D j).hom)).ι).mp
  rw [Category.assoc, quasicategoryCoreMap_ι, ← Category.assoc,
    cocartesianSectionCoreLift_of_vertex_cover_ι]
  exact hs j

/-- 指定した同じ section の族への core の持ち上げは一意。 -/
lemma cocartesianSectionCoreLift_of_vertex_cover_unique
    (m : T ⟶ (quasicategoryCore (kanCocartesianSections p a.hom) : SSet.{u}))
    (hm : m ≫ (quasicategoryCore (kanCocartesianSections p a.hom)).ι = g) :
    m = cocartesianSectionCoreLift_of_vertex_cover p a D i hi g s hs := by
  apply (cancel_mono (quasicategoryCore (kanCocartesianSections p a.hom)).ι).mp
  rw [cocartesianSectionCoreLift_of_vertex_cover_ι]
  exact hm

end SerrePositivity.InfinityCategories
