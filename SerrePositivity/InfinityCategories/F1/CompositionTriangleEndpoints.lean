module

public import SerrePositivity.InfinityCategories.F1.CompositionTriangleFamily

/-!
概要：元の普遍合成三角形の両面と対角の終点を、全パラメーターで計算する。
方針：内ホーンの二辺への制限と標準単体の面の合成則を使う。
規約：対角辺を別の合成に選び直さない。
使われ方：残る第二三角形の外ホーンを、元の対角と標的の辺から構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の辺への定値族の終点は、その元の終点に定値。 -/
lemma edgeFamily_target {T X : SSet.{u}} {x z : X _⦋0⦌} (g : X.Edge x z) :
    (stdSimplex.δ (0 : Fin 2) ▷ T) ≫ fst (Δ[1] : SSet.{u}) T ≫
        SSet.yonedaEquiv.symm g.edge = fst (Δ[0] : SSet.{u}) T ≫ SSet.yonedaEquiv.symm z := by
  rw [← Category.assoc, whiskerRight_fst, Category.assoc]
  congr 1
  apply SSet.yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact g.tgt_eq

/-- 元の普遍合成三角形の最初の面は、元の第一辺に全パラメーターで定値。 -/
lemma compositionTriangleEvaluation_first {X : SSet.{u}} {x y z : X _⦋0⦌}
    (e : X.Edge x y) (f : X.Edge y z) :
    (stdSimplex.δ (2 : Fin 3) ▷ compositionTriangleSpace e f) ≫
        compositionTriangleEvaluation e f =
      fst (Δ[1] : SSet.{u}) (compositionTriangleSpace e f) ≫ SSet.yonedaEquiv.symm e.edge := by
  calc
    _ = (horn₂₁.ι₀₁ ▷ compositionTriangleSpace e f) ≫
        ((horn 2 1).ι ▷ compositionTriangleSpace e f) ≫ compositionTriangleEvaluation e f := by
      rw [← Category.assoc, ← comp_whiskerRight, horn.ι_ι]
    _ = _ := by rw [compositionTriangleEvaluation_horn]
    _ = _ := by
      rw [← Category.assoc, whiskerRight_fst, Category.assoc, composableEdgeHorn_first]

/-- 元の普遍合成三角形の最後の面は、元の第二辺に全パラメーターで定値。 -/
lemma compositionTriangleEvaluation_last {X : SSet.{u}} {x y z : X _⦋0⦌}
    (e : X.Edge x y) (f : X.Edge y z) :
    (stdSimplex.δ (0 : Fin 3) ▷ compositionTriangleSpace e f) ≫
        compositionTriangleEvaluation e f =
      fst (Δ[1] : SSet.{u}) (compositionTriangleSpace e f) ≫ SSet.yonedaEquiv.symm f.edge := by
  calc
    _ = (horn₂₁.ι₁₂ ▷ compositionTriangleSpace e f) ≫
        ((horn 2 1).ι ▷ compositionTriangleSpace e f) ≫ compositionTriangleEvaluation e f := by
      rw [← Category.assoc, ← comp_whiskerRight, horn.ι_ι]
    _ = _ := by rw [compositionTriangleEvaluation_horn]
    _ = _ := by
      rw [← Category.assoc, whiskerRight_fst, Category.assoc, composableEdgeHorn_last]

/-- 元の普遍合成三角形の対角の終点は、元の第二辺の終点に定値。 -/
lemma compositionTriangleEvaluation_diagonal_target {X : SSet.{u}} {x y z : X _⦋0⦌}
    (e : X.Edge x y) (f : X.Edge y z) :
    (stdSimplex.δ (0 : Fin 2) ▷ compositionTriangleSpace e f) ≫
        (stdSimplex.δ (1 : Fin 3) ▷ compositionTriangleSpace e f) ≫
        compositionTriangleEvaluation e f =
      fst (Δ[0] : SSet.{u}) (compositionTriangleSpace e f) ≫ SSet.yonedaEquiv.symm z := by
  have hδ : (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫
      stdSimplex.δ (1 : Fin 3) = stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    decide
  rw [← Category.assoc, ← comp_whiskerRight, hδ, comp_whiskerRight, Category.assoc,
    compositionTriangleEvaluation_last, edgeFamily_target]

/-- 同じ全合成三角形を任意のパラメーターの族で引くと、元の延長空間の評価に一致する。 -/
lemma compositionTriangleEvaluation_precomp {T X : SSet.{u}} {x y z : X _⦋0⦌}
    (e : X.Edge x y) (f : X.Edge y z) (a : T ⟶ compositionTriangleSpace e f) :
    (Δ[2] ◁ a) ≫ compositionTriangleEvaluation e f = innerTriangleExtensionUncurry a := by
  unfold compositionTriangleEvaluation innerTriangleExtensionUncurry
  rw [uncurry_natural_left]

end SerrePositivity.InfinityCategories
