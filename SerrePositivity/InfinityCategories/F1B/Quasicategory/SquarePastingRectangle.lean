module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.F1B.Quasicategory
open SerrePositivity.KST.LocalizingInvariants

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
    Nonempty (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle L R b t) := by
  let a := _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquarePastingHorn.diagram L R h
  have hend (i : Fin 2) (τ : (Δ[2] : SSet.{u}) ⟶ X)
      (hL : _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquarePastingHorn.transposed L ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i) =
        stdSimplex.δ (2 : Fin 3) ≫ τ)
      (hR : _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquarePastingHorn.transposed R ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i) =
        stdSimplex.δ (0 : Fin 3) ≫ τ) :
      prismEndpoint i (horn 2 1 : SSet.{u}) ≫ uncurry a = (horn 2 1).ι ≫ τ := by
    rw [← curry_evaluateFunctorAt_interval, curry_uncurry]
    apply horn₂₁.isPushout.hom_ext
    · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquarePastingHorn.diagram_left, hL, ← Category.assoc,
        horn.ι_ι]
    · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquarePastingHorn.diagram_right, hR, ← Category.assoc,
        horn.ι_ι]
  obtain ⟨F, hF, h₀, h₁⟩ := prism_extend_innerHorn_with_endpoints (1 : Fin 3)
    (by decide) (by decide) (uncurry a) b t
    (hend 0 b ((_root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquarePastingHorn.transposed_bottom L).trans hbL)
      ((_root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquarePastingHorn.transposed_bottom R).trans hbR))
    (hend 1 t ((_root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquarePastingHorn.transposed_top L).trans htL)
      ((_root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquarePastingHorn.transposed_top R).trans htR))
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
  · rw [hface 2 horn₂₁.ι₀₁ (horn.ι_ι _ _ _), _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquarePastingHorn.diagram_left]
    rw [_root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquarePastingHorn.transposed, uncurry_curry, ← Category.assoc,
      SymmetricCategory.symmetry, Category.id_comp]
  · rw [hface 0 horn₂₁.ι₁₂ (horn.ι_ι _ _ _), _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquarePastingHorn.diagram_right]
    rw [_root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquarePastingHorn.transposed, uncurry_curry, ← Category.assoc,
      SymmetricCategory.symmetry, Category.id_comp]
  · exact h₀
  · exact h₁

end SerrePositivity.InfinityCategories.F1B.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquarePastingRectangle := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.nonempty_squarePastingRectangle := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.nonempty_squarePastingRectangle

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquarePastingRectangle._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquarePastingRectangle._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle._sizeOf_inst

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquarePastingRectangle.bottom_eq := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle.bottom_eq

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquarePastingRectangle.casesOn := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquarePastingRectangle.ctorIdx := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle.diagram (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquarePastingRectangle.diagram := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle.diagram

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquarePastingRectangle.left_eq := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle.left_eq

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquarePastingRectangle.mk := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquarePastingRectangle.noConfusion := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquarePastingRectangle.noConfusionType := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquarePastingRectangle.rec := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquarePastingRectangle.recOn := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle.recOn

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquarePastingRectangle.right_eq := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle.right_eq

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquarePastingRectangle.top_eq := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle.top_eq

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquarePastingRectangle.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquarePastingRectangle.mk.inj := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquarePastingRectangle.mk.injEq := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquarePastingRectangle.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquarePastingRectangle.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquarePastingRectangle.mk.sizeOf_spec
