module

public import SerrePositivity.InfinityCategories.Core.Quasicategory.SquarePastingHorn

/-!
概要：隣接する二つの正方形を、指定した上下の合成三角形を保って長方形へ延長する。
方針：内ホーン上の矢印族を、両端固定の prism 充填で延長する。
規約：二次の合成証人も保持。使われ方：Verdier 列の比較と pullback の貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

structure SquarePastingRectangle {X : SSet.{u}}
    (L R : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) (b t : (Δ[2] : SSet.{u}) ⟶ X) where
  diagram : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ X
  left_eq : pastingSquare diagram 2 = L
  right_eq : pastingSquare diagram 0 = R
  bottom_eq : pastingBottomTriangle diagram = b
  top_eq : pastingTopTriangle diagram = t

lemma nonempty_squarePastingRectangle {X : SSet.{u}} [Quasicategory X]
    (L R : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X)
    (h : squareRightEdge ≫ L = squareLeftEdge ≫ R)
    (b t : (Δ[2] : SSet.{u}) ⟶ X)
    (hbL : squareBottomEdge ≫ L = stdSimplex.δ (2 : Fin 3) ≫ b)
    (hbR : squareBottomEdge ≫ R = stdSimplex.δ (0 : Fin 3) ≫ b)
    (htL : squareTopEdge ≫ L = stdSimplex.δ (2 : Fin 3) ≫ t)
    (htR : squareTopEdge ≫ R = stdSimplex.δ (0 : Fin 3) ≫ t) :
    Nonempty (SquarePastingRectangle L R b t) := by
  let a := SquarePastingHorn.diagram L R h
  have hend (i : Fin 2) (τ : (Δ[2] : SSet.{u}) ⟶ X)
      (hL : SquarePastingHorn.transposed L ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i) =
        stdSimplex.δ (2 : Fin 3) ≫ τ)
      (hR : SquarePastingHorn.transposed R ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i) =
        stdSimplex.δ (0 : Fin 3) ≫ τ) :
      prismEndpoint i (horn 2 1 : SSet.{u}) ≫ uncurry a = (horn 2 1).ι ≫ τ := by
    rw [← curry_evaluateFunctorAt_interval, curry_uncurry]
    apply horn₂₁.isPushout.hom_ext
    · rw [← Category.assoc, SquarePastingHorn.diagram_left, hL, ← Category.assoc,
        horn.ι_ι]
    · rw [← Category.assoc, SquarePastingHorn.diagram_right, hR, ← Category.assoc,
        horn.ι_ι]
  obtain ⟨F, hF, h₀, h₁⟩ := prism_extend_innerHorn_with_endpoints (1 : Fin 3)
    (by decide) (by decide) (uncurry a) b t
    (hend 0 b ((SquarePastingHorn.transposed_bottom L).trans hbL)
      ((SquarePastingHorn.transposed_bottom R).trans hbR))
    (hend 1 t ((SquarePastingHorn.transposed_top L).trans htL)
      ((SquarePastingHorn.transposed_top R).trans htR))
  let G := (β_ (Δ[2] : SSet.{u}) Δ[1]).hom ≫ F
  have hface (j : Fin 3) (e : (Δ[1] : SSet.{u}) ⟶ (horn 2 1 : SSet.{u}))
      (he : e ≫ (horn 2 1).ι = stdSimplex.δ j) :
      pastingSquare G j = (β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ uncurry (e ≫ a) := by
    rw [uncurry_natural_left]
    change (stdSimplex.δ j ▷ (Δ[1] : SSet.{u})) ≫
      (β_ (Δ[2] : SSet.{u}) Δ[1]).hom ≫ F = _
    rw [← he, comp_whiskerRight, Category.assoc, ← hF]
    rfl
  refine ⟨⟨G, ?_, ?_, ?_, ?_⟩⟩
  · rw [hface 2 horn₂₁.ι₀₁ (horn.ι_ι _ _ _), SquarePastingHorn.diagram_left]
    rw [SquarePastingHorn.transposed, uncurry_curry, ← Category.assoc,
      SymmetricCategory.symmetry, Category.id_comp]
  · rw [hface 0 horn₂₁.ι₁₂ (horn.ι_ι _ _ _), SquarePastingHorn.diagram_right]
    rw [SquarePastingHorn.transposed, uncurry_curry, ← Category.assoc,
      SymmetricCategory.symmetry, Category.id_comp]
  · exact h₀
  · exact h₁

end SerrePositivity.KST.LocalizingInvariants
