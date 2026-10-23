module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.SectionColimitDescent
public import SerrePositivity.InfinityCategories.F1.Cocartesian.SectionCoreVertexDescentLaws

/-!
概要：整合する cocartesian section の core の族を、元の余極限へ厳密に貼り合わせる。
方針：まず元の section の族を貼り、余極限の頂点被覆で core への所属を回収する。
規約：元の全空間、底上の図式と全パラメーターを保持する。
使われ方：区間 Hom 比較の境界とセルに沿う降下。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 底上の図式の余極限の各脚は、全ての元の頂点を被覆する。 -/
lemma cocartesianSectionColimit_vertex_cover {J : Type v} [Category.{w} J] [Small.{u} J]
    {B : SSet.{u}} {D : J ⥤ Over B} (c : Cocone D)
    (hc : IsColimit ((Over.forget B).mapCocone c)) (x : c.pt.left _⦋0⦌) :
    ∃ j y, (c.ι.app j).left.app (Opposite.op ⦋0⦌) y = x := by
  let ev := (evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋0⦌)
  exact Types.jointly_surjective _ (isColimitOfPreserves ev hc) x

/-- core の局所的な族の整合性は、元の section の族の厳密な整合性を与える。 -/
lemma cocartesianSectionCoreFamily_underlying_compatible {J : Type v} [Category.{w} J]
    {T E B : SSet.{u}} (p : E ⟶ B) (D : J ⥤ Over B)
    (s : ∀ j, T ⟶ (quasicategoryCore (kanCocartesianSections p (D.obj j).hom) : SSet.{u}))
    (hs : ∀ {j k} (f : j ⟶ k), s j =
      s k ≫ quasicategoryCoreMap (kanCocartesianSectionsPre p (D.map f)))
    {j k : J} (f : j ⟶ k) :
    s j ≫ (quasicategoryCore (kanCocartesianSections p (D.obj j).hom)).ι =
      (s k ≫ (quasicategoryCore (kanCocartesianSections p (D.obj k).hom)).ι) ≫
        kanCocartesianSectionsPre p (D.map f) := by
  rw [hs f, Category.assoc, quasicategoryCoreMap_ι, ← Category.assoc]

/-- 各項上の元の core の族を、同じ余極限上の core の族へ貼る。 -/
def cocartesianSectionCoreFamilyColimitLift {J : Type v} [Category.{w} J] [Small.{u} J]
    {T E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [InnerFibration p]
    {D : J ⥤ Over B} (c : Cocone D) (hc : IsColimit ((Over.forget B).mapCocone c))
    (s : ∀ j, T ⟶ (quasicategoryCore (kanCocartesianSections p (D.obj j).hom) : SSet.{u}))
    (hs : ∀ {j k} (f : j ⟶ k), s j =
      s k ≫ quasicategoryCoreMap (kanCocartesianSectionsPre p (D.map f))) :
    T ⟶ (quasicategoryCore (kanCocartesianSections p c.pt.hom) : SSet.{u}) :=
  cocartesianSectionCoreLift_of_vertex_cover p c.pt D.obj c.ι.app
    (cocartesianSectionColimit_vertex_cover c hc)
    (cocartesianSectionFamilyColimitLift p c hc
      (fun j ↦ s j ≫ (quasicategoryCore (kanCocartesianSections p (D.obj j).hom)).ι)
      (cocartesianSectionCoreFamily_underlying_compatible p D s hs)) s
    (fun j ↦ cocartesianSectionFamilyColimitLift_fac p c hc _ _ j)

end SerrePositivity.InfinityCategories
