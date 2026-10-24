module
public import SerrePositivity.InfinityCategories.Core.UniverseLimits

/-! # Under slice の図式同型による再添字付け

概要：図式の形状の同型は実 slice の同型と普遍錐の比較を与える。
方針：join の固定因子への前合成を全単体で定義し、逆同型で戻す。
規約：標的の quasicategory 性は不要。使われ方：標準形状の宇宙比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial

/-- 形状の同型は実 slice を同型にする。 -/
def sliceUnderReindexIso {K L X : SSet.{u}} (e : L ≅ K) (p : K ⟶ X) :
    sliceUnder p ≅ sliceUnder (e.hom ≫ p) where
  hom := {
    app n := ↾fun s => ⟨joinMap e.hom (𝟙 _) ≫ s.val, by
      rw [← Category.assoc, joinInl_joinMap, Category.assoc, s.property]⟩
    naturality _ _ α := by
      ext s
      apply Subtype.ext
      change joinMap e.hom (𝟙 _) ≫
        (joinMap (𝟙 _) (stdSimplex.map α.unop) ≫ s.val) =
          joinMap (𝟙 _) (stdSimplex.map α.unop) ≫ (joinMap e.hom (𝟙 _) ≫ s.val)
      simp only [← Category.assoc, ← joinMap_comp, Category.id_comp, Category.comp_id] }
  inv := {
    app n := ↾fun s => ⟨joinMap e.inv (𝟙 _) ≫ s.val, by
      rw [← Category.assoc, joinInl_joinMap, Category.assoc, s.property,
        ← Category.assoc, e.inv_hom_id, Category.id_comp]⟩
    naturality _ _ α := by
      ext s
      apply Subtype.ext
      change joinMap e.inv (𝟙 _) ≫
        (joinMap (𝟙 _) (stdSimplex.map α.unop) ≫ s.val) =
          joinMap (𝟙 _) (stdSimplex.map α.unop) ≫ (joinMap e.inv (𝟙 _) ≫ s.val)
      simp only [← Category.assoc, ← joinMap_comp, Category.id_comp, Category.comp_id] }
  hom_inv_id := by
    ext n s
    apply Subtype.ext
    change joinMap e.inv (𝟙 _) ≫ (joinMap e.hom (𝟙 _) ≫ s.val) = s.val
    rw [← Category.assoc, ← joinMap_comp, Category.id_comp, e.inv_hom_id,
      joinMap_id, Category.id_comp]
  inv_hom_id := by
    ext n s
    apply Subtype.ext
    change joinMap e.hom (𝟙 _) ≫ (joinMap e.inv (𝟙 _) ≫ s.val) = s.val
    rw [← Category.assoc, ← joinMap_comp, Category.id_comp, e.hom_inv_id,
      joinMap_id, Category.id_comp]

/-- 実錐の形状を同型で引き戻す。 -/
def JoinCocone.reindexIso {K L X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCocone p) (e : L ≅ K) : JoinCocone (e.hom ≫ p) :=
  (sliceUnderReindexIso e p).hom.app (Opposite.op ⦋0⦌) c

/-- 形状同型に沿う再添字付けは普遍性を保ち反映する。 -/
lemma isColimitCone_iff_reindexIso {K L X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCocone p) (e : L ≅ K) :
    IsColimitCone c ↔ IsColimitCone (c.reindexIso e) :=
  isInitialVertex_iff_of_isIso (sliceUnderReindexIso e p).hom c

end SerrePositivity.InfinityCategories
