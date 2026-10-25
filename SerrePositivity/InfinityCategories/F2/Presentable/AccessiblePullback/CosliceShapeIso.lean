module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.FixedSourceExtension

/-!
概要：固定図式の形状同型による coslice の厳密な同型。
方針：固定因子の順逆の joinMap による制限を全次数で構成する。
規約：元の可変因子と全高次成分を保持する。
使われ方：Ind 内の相対因子化を固定始域の coslice へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：形状同型に沿った固定図式の coslice は元の coslice と厳密に同型。
方針：固定因子の順逆の写像で全余錐を制限する。
規約：可変終点と全単体を保持する。
使われ方：宇宙同型で展開した固定入力を元の coslice へ戻す。 -/
def cosliceShapeIso {K L C : SSet.{u}} (e : K ≅ L) (p : L ⟶ C) :
    sliceUnder p ≅ sliceUnder (e.hom ≫ p) where
  hom := sliceUnderRestrict p e.hom
  inv :=
    { app := fun n ↦ ↾fun σ ↦ ⟨joinMap e.inv (𝟙 (Δ[n.unop.len] : SSet.{u})) ≫ σ.val, by
        rw [← Category.assoc, joinInl_joinMap, Category.assoc, σ.property,
          e.inv_hom_id_assoc]⟩
      naturality := by
        intro m n α
        apply ConcreteCategory.hom_ext
        intro σ
        apply Subtype.ext
        symm
        change joinMap (𝟙 L) (SSet.stdSimplex.map α.unop) ≫
            (joinMap e.inv (𝟙 _) ≫ σ.val) =
          joinMap e.inv (𝟙 _) ≫ (joinMap (𝟙 K) (SSet.stdSimplex.map α.unop) ≫ σ.val)
        rw [← Category.assoc, ← joinMap_comp, Category.id_comp, Category.comp_id,
          ← Category.assoc, ← joinMap_comp, Category.id_comp, Category.comp_id] }
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro σ
    apply Subtype.ext
    change joinMap e.inv (𝟙 _) ≫ (joinMap e.hom (𝟙 _) ≫ σ.val) = σ.val
    rw [← Category.assoc, ← joinMap_comp, e.inv_hom_id, Category.id_comp,
      joinMap_id, Category.id_comp]
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro σ
    apply Subtype.ext
    change joinMap e.hom (𝟙 _) ≫ (joinMap e.inv (𝟙 _) ≫ σ.val) = σ.val
    rw [← Category.assoc, ← joinMap_comp, e.hom_inv_id, Category.id_comp,
      joinMap_id, Category.id_comp]

/-- 概要：形状同型の coslice 比較の順射は全余錐値の元の制限。
方針：全次数での定義を読む。
規約：全単体上の厳密な値。
使われ方：相対因子化の固定境界の輸送。 -/
lemma cosliceShapeIso_hom_val {K L C : SSet.{u}} (e : K ≅ L) (p : L ⟶ C)
    {n : ℕ} (σ : (sliceUnder p) _⦋n⦌) :
    ((cosliceShapeIso e p).hom.app (Opposite.op ⦋n⦌) σ).val =
      joinMap e.hom (𝟙 Δ[n]) ≫ σ.val := rfl

/-- 概要：形状同型の coslice 比較の逆射も全余錐値の元の逆制限。
方針：全次数での逆写像の定義を読む。
規約：全単体上の厳密な値。
使われ方：元の相対余錐と比較辺の回収。 -/
lemma cosliceShapeIso_inv_val {K L C : SSet.{u}} (e : K ≅ L) (p : L ⟶ C)
    {n : ℕ} (σ : (sliceUnder (e.hom ≫ p)) _⦋n⦌) :
    ((cosliceShapeIso e p).inv.app (Opposite.op ⦋n⦌) σ).val =
      joinMap e.inv (𝟙 Δ[n]) ≫ σ.val := rfl

/-- 概要：形状同型の coslice 比較は元の可変終点を保つ。
方針：全余錐の右境界に制限し、join の右包含の自然性を使う。
規約：元の全射影の等式。
使われ方：同じ filtered 余極限の底への射影の回収。 -/
lemma cosliceShapeIso_projection {K L C : SSet.{u}} (e : K ≅ L) (p : L ⟶ C) :
    (cosliceShapeIso e p).hom ≫ sliceUnderProjection (e.hom ≫ p) =
      sliceUnderProjection p := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro σ
  change SSet.yonedaEquiv (joinInr K Δ[n.unop.len] ≫ (joinMap e.hom (𝟙 _) ≫ σ.val)) =
    SSet.yonedaEquiv (joinInr L Δ[n.unop.len] ≫ σ.val)
  rw [← Category.assoc, joinInr_joinMap, Category.id_comp]

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
