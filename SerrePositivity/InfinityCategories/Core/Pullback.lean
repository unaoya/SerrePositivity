module

public import SerrePositivity.InfinityCategories.Core.Square

/-!
概要：cospan の極限としての引き戻し四角形。
方針：Δ[0]⋆Λ[2,2] と正方形の同型で四角形を錐に直し、A2f の極限性を適用する。
規約：右辺と上辺が cospan、左下の座標 (0,0) が錐頂点。
使われ方：HTT §1.2.13、Kerodon §7.1・§7.3 の引き戻し。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories

/-- 概要：正方形の右辺 (1,t)。
方針：第一座標を終点、第二座標を恒等にする。
規約：向きは (1,0) から (1,1)。
使われ方：HTT §1.2.13、Kerodon §7.1 の引き戻しの cospan の零番目の脚。 -/
def squareRightEdge : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] :=
  CartesianMonoidalCategory.lift (SSet.const (stdSimplex.obj₀Equiv.symm 1)) (𝟙 Δ[1])

/-- 概要：正方形の上辺 (t,1)。
方針：第一座標を恒等、第二座標を終点にする。
規約：向きは (0,1) から (1,1)。
使われ方：HTT §1.2.13、Kerodon §7.1 の引き戻しの cospan の一番目の脚。 -/
def squareTopEdge : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] :=
  CartesianMonoidalCategory.lift (𝟙 Δ[1]) (SSet.const (stdSimplex.obj₀Equiv.symm 1))

/-- 概要：下側の三角形の最後の辺は正方形の右辺。
方針：Yoneda で有限頂点写像の計算へ帰着する。
規約：三角形の番号は 1、面は δ₀。
使われ方：HTT §1.2.13 の cospan の向きの確認。 -/
lemma squareTriangle_rightEdge :
    stdSimplex.δ (0 : Fin 3) ≫ squareTriangle.{u} 1 = squareRightEdge := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

/-- 概要：上側の三角形の最後の辺は正方形の上辺。
方針：Yoneda で有限頂点写像の計算へ帰着する。
規約：三角形の番号は 0、面は δ₀。
使われ方：HTT §1.2.13 の cospan の向きの確認。 -/
lemma squareTriangle_topEdge :
    stdSimplex.δ (0 : Fin 3) ≫ squareTriangle.{u} 0 = squareTopEdge := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

/-- 概要：正方形の右辺と上辺からなる cospan の包含。
方針：join の右包含を cospan の錐と正方形の同型で写す。
規約：ホーンは Λ[2,2]。
使われ方：HTT §1.2.13、Kerodon §7.1 の四角形から cospan への制限。 -/
noncomputable def cospanSquareBoundary : (horn 2 2 : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] :=
  joinInr Δ[0] (horn 2 2 : SSet.{u}) ≫ cospanConeSquareIso.hom

/-- 概要：cospan の零番目の脚は正方形の右辺に写る。
方針：join の包含の自然性と二つの三角形の比較を使う。
規約：ホーンの辺は 0→2。
使われ方：HTT §1.2.13 の引き戻しの図式の確認。 -/
lemma cospanSquareBoundary_rightEdge :
    horn₂₂.ι₀₂ ≫ cospanSquareBoundary.{u} = squareRightEdge := by
  calc
    _ = joinInr (Δ[0] : SSet.{u}) Δ[1] ≫
        (joinMap (𝟙 Δ[0]) horn₂₂.ι₀₂ ≫ cospanConeSquareIso.hom) := by
      rw [← Category.assoc, joinInr_joinMap, Category.assoc]
      rfl
    _ = stdSimplex.δ (0 : Fin 3) ≫ (cospanConeTriangleLeft ≫ cospanConeSquareIso.hom) := by
      rw [← joinStdSimplexIso_one_inr]
      simp only [cospanConeTriangleLeft, Category.assoc, Iso.hom_inv_id_assoc]
    _ = squareRightEdge := by rw [cospanConeSquareIso_left, squareTriangle_rightEdge]

/-- 概要：cospan の一番目の脚は正方形の上辺に写る。
方針：join の包含の自然性と二つの三角形の比較を使う。
規約：ホーンの辺は 1→2。
使われ方：HTT §1.2.13 の引き戻しの図式の確認。 -/
lemma cospanSquareBoundary_topEdge :
    horn₂₂.ι₁₂ ≫ cospanSquareBoundary.{u} = squareTopEdge := by
  calc
    _ = joinInr (Δ[0] : SSet.{u}) Δ[1] ≫
        (joinMap (𝟙 Δ[0]) horn₂₂.ι₁₂ ≫ cospanConeSquareIso.hom) := by
      rw [← Category.assoc, joinInr_joinMap, Category.assoc]
      rfl
    _ = stdSimplex.δ (0 : Fin 3) ≫ (cospanConeTriangleRight ≫ cospanConeSquareIso.hom) := by
      rw [← joinStdSimplexIso_one_inr]
      simp only [cospanConeTriangleRight, Category.assoc, Iso.hom_inv_id_assoc]
    _ = squareTopEdge := by rw [cospanConeSquareIso_right, squareTriangle_topEdge]

/-- 概要：四角形の右辺と上辺の cospan。
方針：固定したホーンの包含で四角形を制限する。
規約：図式の向きは 0→2←1。
使われ方：HTT §1.2.13、Kerodon §7.1 の引き戻し図式。 -/
noncomputable def pullbackCospan {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    (horn 2 2 : SSet.{u}) ⟶ X := cospanSquareBoundary ≫ F

/-- 概要：四角形をその cospan 上の錐へ直す。
方針：cospan の錐と正方形の同型で前合成する。
規約：固定条件は join の右包含との合成である。
使われ方：HTT §1.2.13、Kerodon §7.1 の引き戻しを極限として扱う橋。 -/
noncomputable def pullbackCone {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    JoinCone (pullbackCospan F) :=
  ⟨cospanConeSquareIso.hom ≫ F, by
    simp only [pullbackCospan, cospanSquareBoundary, Category.assoc]⟩

/-- 概要：四角形が引き戻しであることは、対応する cospan の錐が極限錐であること。
方針：正方形と join の同型を通じて A2f の極限性を適用する。
規約：定義自体には quasicategory の仮定は不要。
使われ方：HTT §1.2.13、Kerodon §7.1・§7.3 の引き戻し四角形。 -/
def IsPullbackSquare {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) : Prop := IsLimitCone (pullbackCone F)

/-- 概要：引き戻し四角形の性質は、対応する錐上の slice 射影の trivial Kan fibration 性と同値。
方針：極限錐の trivial Kan fibration による特徴づけを適用する。
規約：slice の基底は右辺と上辺からなる cospan。
使われ方：HTT §1.2.13、Kerodon §7.1 の引き戻しの充填条件。 -/
lemma isPullbackSquare_iff_trivialKanFibration {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    IsPullbackSquare F ↔ TrivialKanFibration
      (sliceOverProjection (X := sliceOver (pullbackCospan F))
        (SSet.yonedaEquiv.symm (pullbackCone F))) :=
  isLimitCone_iff_trivialKanFibration (pullbackCone F)

end SerrePositivity.InfinityCategories
