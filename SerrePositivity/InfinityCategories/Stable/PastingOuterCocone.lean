module
public import SerrePositivity.InfinityCategories.Stable.PastingOuterSpanIso

/-! # 四頂点図式の余錐と外側四角形

概要：長方形の余錐を四頂点図式へ制限すると、外側 span 上で外側四角形の余錐になる。
方針：基底の厳密な一致と終端角の一致を使う。
規約：左四角形の押し出し性による五頂点と四頂点の比較は別途必要。
使われ方：S4 の貼り合わせの外側の普遍性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：長方形の余錐を外側 span に制限すると外側四角形の余錐表示に一致する。
方針：基底では外側 span の包含、終端角では正方形の第一三角形を使う。
規約：値域の図式を選ぶ前の形状の等式。使われ方：外側の押し出し判定。 -/
lemma pastingCornerCocone_outerSpan :
    joinMap (pastingOuterSpanIso.{u}.hom ≫ pastingOuterSpan.ι ≫ pastingOuterBaseToCorner)
      (𝟙 Δ[0]) ≫ pastingCornerCocone =
    spanCoconeSquareIso.hom ≫ (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) := by
  apply stableJoin_prodStdSimplex_hom_ext
  · rw [← Category.assoc, joinInl_joinMap, Category.assoc, pastingCornerCocone_inl]
    have hι : pastingOuterBaseToCorner ≫ pastingCorner.ι = pastingOuterBase.ι := rfl
    rw [Category.assoc, Category.assoc, hι]
    exact pastingOuterSpanIso_hom_ι
  · rw [← Category.assoc, joinInr_joinMap, Category.id_comp]
    have hv : joinInr (horn 2 0 : SSet.{u}) Δ[0] =
        joinInr Δ[1] Δ[0] ≫ (joinStdSimplexIso 1 0).hom ≫ spanCoconeTriangleLeft := by
      simp only [spanCoconeTriangleLeft, Iso.hom_inv_id_assoc]
      rw [joinInr_joinMap, Category.id_comp]
    rw [hv]
    simp only [Category.assoc, reassoc_of% spanCoconeSquareIso_left]
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> decide

/-- 概要：長方形の余錐を四頂点図式へ制限する。
方針：五頂点図式への包含に沿う余錐の制限を使う。
規約：左四角形の余極限頂点を含まない基底。使われ方：外側比較の中間余錐。 -/
def pastingOuterCocone {X : SSet.{u}} (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) :=
  (pastingCocone F).restrict pastingOuterBaseToCorner

/-- 概要：四頂点図式上の長方形の余極限性は外側四角形の押し出し性と同値。
方針：外側 span への制限で判定し、形状の等式で外側四角形の余錐と比較する。
規約：値域は quasicategory、左四角形への仮定は不要。
使われ方：S4 の貼り合わせの外側の普遍性の判定。 -/
lemma pastingOuterCocone_isColimitCone_iff_outer {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    IsColimitCone (pastingOuterCocone F) ↔ IsPushoutSquare (pastingSquare F 1) := by
  refine (pastingOuterBase_isColimitCone_iff_standardSpan (pastingOuterCocone F)).trans ?_
  apply isColimitCone_iff_of_val_eq
  dsimp only [JoinCocone.restrict, pastingOuterCocone, pastingCocone,
    pushoutCocone, pastingSquare]
  rw [← Category.assoc, ← Category.assoc, ← joinMap_comp]
  simp only [Category.id_comp]
  rw [Category.assoc pastingOuterSpanIso.hom pastingOuterSpan.ι pastingOuterBaseToCorner,
    pastingCornerCocone_outerSpan, Category.assoc]

end SerrePositivity.InfinityCategories
