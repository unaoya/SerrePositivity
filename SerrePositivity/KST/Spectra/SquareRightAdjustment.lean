module

public import SerrePositivity.KST.Spectra.ExponentialRelativeComposition

/-!
概要：正方形の右辺を両端固定の実変形に沿って修正し、残り三辺を厳密に保つ。
方針：正方形の座標を交換し、両端への制限 fibration 上で元の辺と変形を合成する。
規約：標的の Kan 性を使う。使われ方：段調整の正方形と相対帰納正方形の貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.SquareAdjustment

/-- 正方形の左辺の挿入。元のホモトピーの時間方向は保持する。 -/
def leftSide : (Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) :=
  SSet.ι₀ ≫ (β_ (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).hom

/-- 正方形の右辺の挿入。 -/
def rightSide : (Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) :=
  SSet.ι₁ ≫ (β_ (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).hom

/-- 座標交換後の左辺は、交換前の始辺。 -/
lemma leftSide_swap {E : SSet.{u}}
    (F : (Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ E) :
    leftSide ≫ ((β_ (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).hom ≫ F) = SSet.ι₀ ≫ F := by
  change (SSet.ι₀ ≫ (β_ _ _).hom) ≫ ((β_ _ _).hom ≫ F) = _
  rw [Category.assoc, ← Category.assoc (β_ _ _).hom (β_ _ _).hom F,
    SymmetricCategory.symmetry, Category.id_comp]

/-- 座標交換後の右辺は、交換前の終辺。 -/
lemma rightSide_swap {E : SSet.{u}}
    (F : (Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ E) :
    rightSide ≫ ((β_ (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).hom ≫ F) = SSet.ι₁ ≫ F := by
  change (SSet.ι₁ ≫ (β_ _ _).hom) ≫ ((β_ _ _).hom ≫ F) = _
  rw [Category.assoc, ← Category.assoc (β_ _ _).hom (β_ _ _).hom F,
    SymmetricCategory.symmetry, Category.id_comp]

/-- 全境界への制限が同じなら、左右の同じ実辺への制限も同じ。 -/
lemma sides_eq_of_boundary_eq {E : SSet.{u}}
    {F G : (Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ E}
    (h : (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ F =
      (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ G) :
    leftSide ≫ F = leftSide ≫ G ∧ rightSide ≫ F = rightSide ≫ G := by
  have hf (j : Fin 2) : stdSimplex.δ j ▷ (Δ[1] : SSet.{u}) ≫ F =
      stdSimplex.δ j ▷ (Δ[1] : SSet.{u}) ≫ G := by
    have he := congrArg (boundary.ι j ▷ (Δ[1] : SSet.{u}) ≫ ·) h
    simpa only [← comp_whiskerRight_assoc, boundary.ι_ι] using he
  have hl : leftSide.{u} = lift (stdSimplex.isTerminalObj₀.from _) (𝟙 _) ≫
      stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u}) := by
    apply CartesianMonoidalCategory.hom_ext <;> rfl
  have hr : rightSide.{u} = lift (stdSimplex.isTerminalObj₀.from _) (𝟙 _) ≫
      stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u}) := by
    apply CartesianMonoidalCategory.hom_ext <;> rfl
  constructor
  · rw [hl, Category.assoc, Category.assoc, hf]
  · rw [hr, Category.assoc, Category.assoc, hf]

variable {E : SSet.{u}} {f g : (Δ[1] : SSet.{u}) ⟶ E} (H : SSet.Homotopy f g)

/-- 正方形を左右方向のホモトピーとして読み、元の同じ四辺を保持する。 -/
def flip : SSet.Homotopy (leftSide ≫ H.h) (rightSide ≫ H.h) where
  h := (β_ (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).hom ≫ H.h
  h₀ := by rfl
  h₁ := by rfl
  rel := by ext m ⟨⟨s, hs⟩, r⟩; exact hs.elim

variable [KanComplex E] {k : (Δ[1] : SSet.{u}) ⟶ E}
  (V : SSet.Homotopy (rightSide ≫ H.h) k)
  (hV : (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ V.h =
    fst (∂Δ[1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (boundary 1).ι ≫ rightSide ≫ H.h)

/-- 正方形の左右方向の辺と実変形を、元の両端射影を厳密に保って合成する。 -/
def rightAdjustmentComposite : ExponentialPaths.RelativeComposite (boundary 1).ι (flip H) V :=
  ExponentialPaths.RelativeComposite.choose _ _ _ hV

/-- 合成区間を元の向きへ戻した正方形の始辺は、元の始辺そのもの。 -/
lemma adjusted_zero : SSet.ι₀ ≫
    ((β_ (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).hom ≫
      (rightAdjustmentComposite H V hV).homotopy.h) = f := by
  change leftSide ≫ (rightAdjustmentComposite H V hV).homotopy.h = f
  have h := (sides_eq_of_boundary_eq (rightAdjustmentComposite H V hV).restriction).1
  exact h.trans ((leftSide_swap H.h).trans H.h₀)

/-- 合成区間を元の向きへ戻した正方形の終辺も、元の終辺そのもの。 -/
lemma adjusted_one : SSet.ι₁ ≫
    ((β_ (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).hom ≫
      (rightAdjustmentComposite H V hV).homotopy.h) = g := by
  change rightSide ≫ (rightAdjustmentComposite H V hV).homotopy.h = g
  have h := (sides_eq_of_boundary_eq (rightAdjustmentComposite H V hV).restriction).2
  exact h.trans ((rightSide_swap H.h).trans H.h₁)

/-- 元の二辺の間の実ホモトピーとして、右辺だけを修正した正方形を回収する。 -/
def adjustRight : SSet.Homotopy f g where
  h := (β_ (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).hom ≫
    (rightAdjustmentComposite H V hV).homotopy.h
  h₀ := adjusted_zero H V hV
  h₁ := adjusted_one H V hV
  rel := by ext m ⟨⟨s, hs⟩, r⟩; exact hs.elim

/-- 修正後の左辺は、元の同じ左辺を保持する。 -/
lemma adjustRight_left : leftSide ≫ (adjustRight H V hV).h = leftSide ≫ H.h := by
  exact (leftSide_swap (rightAdjustmentComposite H V hV).homotopy.h).trans
    (rightAdjustmentComposite H V hV).homotopy.h₀

/-- 修正後の右辺は、元の実変形の同じ終点区間そのもの。 -/
lemma adjustRight_right : rightSide ≫ (adjustRight H V hV).h = k := by
  exact (rightSide_swap (rightAdjustmentComposite H V hV).homotopy.h).trans
    (rightAdjustmentComposite H V hV).homotopy.h₁

end SerrePositivity.KST.Spectra.SquareAdjustment
