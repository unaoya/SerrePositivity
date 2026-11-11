module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence

/-!
概要：三因子の整合と評価比較の正方形から、同じ三角形の整合を回収する。
方針：指定された二つの評価比較だけを同型の結合則で消去する。
規約：元の三角形と全比較を保持。使われ方：元の零面の値と指定三角形の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 二つの評価比較を通すと、同じ三角形の指定辺との整合が得られる。 -/
lemma iso_triangle_square_cancel {C : Type u} [Category.{v} C]
    {a b r₀ r₁ e₀ e₁ : C} (A : a ≅ b) (J : b ≅ r₀) (K : a ≅ r₁)
    (T : e₀ ≅ e₁) (E : e₀ ≅ r₀) (F : e₁ ≅ r₁) (R : r₀ ≅ r₁)
    (h₁ : A ≪≫ J ≪≫ R = K) (h₂ : T ≪≫ F = E ≪≫ R) :
    A ≪≫ (J ≪≫ E.symm) ≪≫ T = K ≪≫ F.symm := by
  have hR : E.symm ≪≫ T ≪≫ F = R := by
    rw [h₂]
    simp only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]
  calc
    _ = (A ≪≫ J ≪≫ (E.symm ≪≫ T ≪≫ F)) ≪≫ F.symm := by
      simp only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
    _ = (A ≪≫ J ≪≫ R) ≪≫ F.symm := by rw [hR]
    _ = _ := by rw [h₁]

/-- 同じ二因子の可換正方形を単体集合の射で写す。 -/
lemma vertexIso_map_square {X Y : SSet.{u}} {a b c d : X _⦋0⦌}
    (f : VertexIso a b) (g : VertexIso b d) (h : VertexIso a c) (i : VertexIso c d)
    (m : X ⟶ Y) (hs : f ≪≫ g = h ≪≫ i) :
    VertexIso.map f m ≪≫ VertexIso.map g m = VertexIso.map h m ≪≫ VertexIso.map i m := by
  simpa only [VertexIso.map, CategoryTheory.Functor.mapIso_trans] using
    congrArg (fun t => VertexIso.map t m) hs

end SerrePositivity.InfinityCategories.F2
