module
public import SerrePositivity.InfinityCategories.Stable.UniverseLimits

/-! # Over slice の図式同型による再添字付け

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
def sliceOverReindexIso {K L X : SSet.{u}} (e : L ≅ K) (p : K ⟶ X) :
    sliceOver p ≅ sliceOver (e.hom ≫ p) where
  hom := {
    app n := ↾fun s => ⟨joinMap (𝟙 _) e.hom ≫ s.val, by
      rw [← Category.assoc, joinInr_joinMap, Category.assoc, s.property]⟩
    naturality _ _ α := by
      ext s
      apply Subtype.ext
      change joinMap (𝟙 _) e.hom ≫
        (joinMap (stdSimplex.map α.unop) (𝟙 _) ≫ s.val) =
          joinMap (stdSimplex.map α.unop) (𝟙 _) ≫ (joinMap (𝟙 _) e.hom ≫ s.val)
      simp only [← Category.assoc, ← joinMap_comp, Category.id_comp, Category.comp_id] }
  inv := {
    app n := ↾fun s => ⟨joinMap (𝟙 _) e.inv ≫ s.val, by
      rw [← Category.assoc, joinInr_joinMap, Category.assoc, s.property,
        ← Category.assoc, e.inv_hom_id, Category.id_comp]⟩
    naturality _ _ α := by
      ext s
      apply Subtype.ext
      change joinMap (𝟙 _) e.inv ≫
        (joinMap (stdSimplex.map α.unop) (𝟙 _) ≫ s.val) =
          joinMap (stdSimplex.map α.unop) (𝟙 _) ≫ (joinMap (𝟙 _) e.inv ≫ s.val)
      simp only [← Category.assoc, ← joinMap_comp, Category.id_comp, Category.comp_id] }
  hom_inv_id := by
    ext n s
    apply Subtype.ext
    change joinMap (𝟙 _) e.inv ≫ (joinMap (𝟙 _) e.hom ≫ s.val) = s.val
    rw [← Category.assoc, ← joinMap_comp, Category.id_comp, e.inv_hom_id,
      joinMap_id, Category.id_comp]
  inv_hom_id := by
    ext n s
    apply Subtype.ext
    change joinMap (𝟙 _) e.hom ≫ (joinMap (𝟙 _) e.inv ≫ s.val) = s.val
    rw [← Category.assoc, ← joinMap_comp, Category.id_comp, e.hom_inv_id,
      joinMap_id, Category.id_comp]

/-- 実錐の形状を同型で引き戻す。 -/
def JoinCone.reindexIso {K L X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (e : L ≅ K) : JoinCone (e.hom ≫ p) :=
  (sliceOverReindexIso e p).hom.app (Opposite.op ⦋0⦌) c

/-- 形状同型に沿う再添字付けは普遍性を保ち反映する。 -/
lemma isLimitCone_iff_reindexIso {K L X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (e : L ≅ K) :
    IsLimitCone c ↔ IsLimitCone (c.reindexIso e) :=
  isTerminalVertex_iff_of_isIso (sliceOverReindexIso e p).hom c

end SerrePositivity.InfinityCategories
