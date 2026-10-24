module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCanonicalRestrictionHom
public import SerrePositivity.InfinityCategories.F2.Idempotent.Retracts

/-!
概要：標準左 Kan 関手の制限の retract を元の全関手圏へ戻す。
方針：制限の Hom 全単射で包含・射影を戻し、分裂等式を忠実性で反映する。
規約：両関手の元の全標準 Kan 条件を要求する。
使われ方：compact 生成圏上の解関手の retract を全域へ延長する。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：二つの標準左 Kan 関手の元の制限間の retract は全域の retract に戻る。
方針：実際の制限関手の Hom 全単射を両方向へ適用する。
規約：分類済みの元の自然変換の分裂を保持する。
使われ方：filtered 生成による余表現可能性の全域化。 -/
def leftCanonicalRestrictionRetraction {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) (F G : C ⟶ D)
    (hF : ∀ c, IsColimitCone (leftKanCanonicalCocone δ F c))
    (hG : ∀ c, IsColimitCone (leftKanCanonicalCocone δ G c))
    (r : Idempotent.VertexRetraction (functorVertex (δ ≫ F)) (functorVertex (δ ≫ G))) :
    Idempotent.VertexRetraction (functorVertex F) (functorVertex G) := by
  let h₁ := F1B.kanLeftCanonicalHomMap_bijective δ F hF G
  let h₂ := F1B.kanLeftCanonicalHomMap_bijective δ G hG F
  let s := Classical.choose (h₁.surjective r.i)
  let t := Classical.choose (h₂.surjective r.r)
  have hs := Classical.choose_spec (h₁.surjective r.i)
  have ht := Classical.choose_spec (h₂.surjective r.r)
  refine ⟨s, t, ?_⟩
  apply (F1B.kanLeftCanonicalHomMap_bijective δ F hF F).injective
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id, hs, ht]
  exact r.retract

end SerrePositivity.InfinityCategories.F2.Presentable
