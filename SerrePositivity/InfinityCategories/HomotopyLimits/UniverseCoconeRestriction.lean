module
public import SerrePositivity.InfinityCategories.Core.ColimitCoconeRestriction

public import SerrePositivity.InfinityCategories.Core.UniverseLimits

/-!
概要：元の全余錐の形状制限と宇宙変更は、同じ全写像として可換。
方針：join の元の形状写像に関する宇宙同型の自然性を使う。
規約：元の形状写像と指定全余錐を保持する。
使われ方：小さい密度形状による局所 Kan 余錐の宇宙変更の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の余錐形状の宇宙比較は、元の可変形状への全射に関して自然。 -/
lemma uliftCoconeShapeIso_inv_leftMap {K L : SSet.{u}} (f : L ⟶ K) (n : ℕ) :
    joinMap ((SSet.uliftFunctor.{v, u}).map f) (𝟙 (Δ[n] : SSet.{max u v})) ≫
      (uliftCoconeShapeIso.{u, v} K n).inv =
    (uliftCoconeShapeIso.{u, v} L n).inv ≫
      (SSet.uliftFunctor.{v, u}).map (joinMap f (𝟙 (Δ[n] : SSet.{u}))) := by
  have h := uliftJoinIso_inv_naturality.{u, v} f (𝟙 (Δ[n] : SSet.{u}))
  rw [(SSet.uliftFunctor.{v, u}).map_id] at h
  dsimp only [uliftCoconeShapeIso, Iso.trans_inv, joinIso, Iso.refl_inv]
  rw [Category.assoc, ← h]
  simp only [← Category.assoc, ← joinMap_comp, Category.id_comp, Category.comp_id]

/-- 元の指定全余錐の制限の持ち上げは、元の持ち上げの同じ形状への制限と一致。 -/
lemma ulift_restrictJoinCocone_val {K L X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCocone p) (f : L ⟶ K) :
    (JoinCocone.ulift.{u, v} (c.restrict f)).val =
      joinMap ((SSet.uliftFunctor.{v, u}).map f) (𝟙 (Δ[0] : SSet.{max u v})) ≫
        (JoinCocone.ulift.{u, v} c).val := by
  change (uliftCoconeShapeIso L 0).inv ≫
      (SSet.uliftFunctor.{v, u}).map (joinMap f (𝟙 _) ≫ c.val) =
    joinMap ((SSet.uliftFunctor.{v, u}).map f) (𝟙 _) ≫
      ((uliftCoconeShapeIso K 0).inv ≫ (SSet.uliftFunctor.{v, u}).map c.val)
  rw [Functor.map_comp, ← Category.assoc, ← uliftCoconeShapeIso_inv_leftMap, Category.assoc]

end SerrePositivity.InfinityCategories.HomotopyLimits
