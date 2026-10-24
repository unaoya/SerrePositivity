module

public import SerrePositivity.InfinityCategories.F2.Ind.DiagramCommaRestriction

/-!
概要：元の全図式 comma の形状制限の恒等則と合成則。
方針：元の C 図式への射影と、元の全余錐の制限を両方照合する。
規約：同型での置換をせず、元の全射の厳密な等号を示す。
使われ方：有限半順序形状の点追加で旧図式と下方図式の共通境界を保持する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：元の図式 comma の形状制限は厳密に合成する。
方針：元の射影と全錐を照合する。規約：全射の等号。使われ方：点追加の共通境界。 -/
lemma diagramCommaRestriction_comp (κ : Cardinal.{u}) {I J K C : SSet.{u}}
    [Quasicategory C] (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ IndInfinity κ C)
    (f : J ⟶ K) (g : I ⟶ J) :
    diagramCommaRestriction κ D f ≫
      diagramCommaRestriction κ ((SSet.uliftFunctor.{u + 1, u}).map f ≫ D) g =
    diagramCommaRestriction κ D (g ≫ f) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, diagramCommaRestriction_projection]
    rw [← Category.assoc, diagramCommaRestriction_projection, Category.assoc,
      ← Functor.map_comp, ← NatTrans.comp_app, ← pre_map]
    have hp := (diagramCommaRestriction_projection κ D (g ≫ f)).symm
    convert hp using 1
    rfl
  · apply sliceOverUncurry_injective
    have hf := diagramCommaRestriction_uncurry κ D f (𝟙 _)
    have hg := diagramCommaRestriction_uncurry κ
      ((SSet.uliftFunctor.{u + 1, u}).map f ≫ D) g (diagramCommaRestriction κ D f)
    have hgf := diagramCommaRestriction_uncurry κ D (g ≫ f) (𝟙 _)
    simp only [Category.id_comp] at hf hgf
    rw [hf, Category.assoc, ← NatTrans.comp_app, ← pre_map, ← Functor.map_comp] at hg
    have h := hg.trans hgf.symm
    convert h using 1 <;> rfl
/-- 概要：恒等形状制限は元の全 comma の恒等射。
方針：元の射影と全錐を照合する。規約：全射の等号。使われ方：点追加の共通境界。 -/
lemma diagramCommaRestriction_id (κ : Cardinal.{u}) {K C : SSet.{u}}
    [Quasicategory C] (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ IndInfinity κ C) :
    diagramCommaRestriction κ D (𝟙 K) = 𝟙 (diagramComma κ D) := by
  apply pullback.hom_ext
  · have h := diagramCommaRestriction_projection κ D (𝟙 K)
    simp only [pre_id, NatTrans.id_app] at h
    rw [(SSet.uliftFunctor.{u + 1, u}).map_id ((ihom K).obj C), Category.comp_id] at h
    convert h using 1
    rfl
  · apply sliceOverUncurry_injective
    have h := diagramCommaRestriction_uncurry κ D (𝟙 K) (𝟙 _)
    have hi : ((pre ((SSet.uliftFunctor.{u + 1, u}).map (𝟙 K))).app
        (IndInfinity κ C)) = 𝟙 _ := by
      rw [(SSet.uliftFunctor.{u + 1, u}).map_id K, pre_id]
      rfl
    simp only [Category.id_comp, hi, Category.comp_id] at h
    convert h using 1
    rfl

end SerrePositivity.InfinityCategories.F2.Ind
