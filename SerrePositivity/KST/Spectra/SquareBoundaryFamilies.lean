module

public import SerrePositivity.KST.Spectra.IntervalBoundaryFamilies
public import SerrePositivity.KST.Spectra.SquareRightAdjustment

/-!
概要：正方形の両端への制限を、同じ左右の実辺の境界族へ厳密に同定する。
方針：二端点の面と正規化した辺の挿入を比較し、元の二つの区間を回収する。
規約：標的の Kan 性は不要。使われ方：指定三角形の指数辺合成と正方形の四辺の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.SquareAdjustment

/-- 始点の面との積は、同じ正規化した左辺への射影。 -/
lemma face_left : stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u}) =
    snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ leftSide := by
  rw [stdSimplex.δ_one_eq_const]
  rfl

/-- 終点の面との積は、同じ正規化した右辺への射影。 -/
lemma face_right : stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u}) =
    snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ rightSide := by
  rw [stdSimplex.δ_zero_eq_const]
  rfl

variable {E : SSet.{u}} (F : (Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ E)

/-- 正方形の境界制限は、元の左右の実辺そのものを束ねた族。 -/
lemma boundary_restriction : (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ F =
    intervalBoundaryFamily (leftSide ≫ F) (rightSide ≫ F) := by
  apply boundary_tensor_hom_ext
  intro j
  simp only [← comp_whiskerRight_assoc, boundary.ι_ι]
  fin_cases j
  · change stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u}) ≫ F =
      boundary.ι (0 : Fin 2) ▷ (Δ[1] : SSet.{u}) ≫
        intervalBoundaryFamily (leftSide ≫ F) (rightSide ≫ F)
    rw [face_right, intervalBoundaryFamily_zero, Category.assoc]
  · change stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u}) ≫ F =
      boundary.ι (1 : Fin 2) ▷ (Δ[1] : SSet.{u}) ≫
        intervalBoundaryFamily (leftSide ≫ F) (rightSide ≫ F)
    rw [face_left, intervalBoundaryFamily_one, Category.assoc]

/-- 指定境界族への制限式から、元の左右の辺との厳密一致を回収する。 -/
lemma sides_of_boundary_restriction {l r : (Δ[1] : SSet.{u}) ⟶ E}
    (h : (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ F = intervalBoundaryFamily l r) :
    leftSide ≫ F = l ∧ rightSide ≫ F = r := by
  have hf (j : Fin 2) := congrArg (boundary.ι j ▷ (Δ[1] : SSet.{u}) ≫ ·) h
  simp only [← comp_whiskerRight_assoc, boundary.ι_ι] at hf
  have hl := hf 1
  have hr := hf 0
  rw [face_left, intervalBoundaryFamily_one, Category.assoc] at hl
  rw [face_right, intervalBoundaryFamily_zero, Category.assoc] at hr
  have section_snd : CartesianMonoidalCategory.lift
      (stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{u})) (𝟙 _) ≫
      snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) = 𝟙 _ := lift_snd _ _
  constructor
  · have he := congrArg (CartesianMonoidalCategory.lift
        (stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{u})) (𝟙 _) ≫ ·) hl
    simpa only [← Category.assoc, section_snd, Category.id_comp] using he
  · have he := congrArg (CartesianMonoidalCategory.lift
        (stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{u})) (𝟙 _) ≫ ·) hr
    simpa only [← Category.assoc, section_snd, Category.id_comp] using he

/-- 指定した両端境界族を持つ正方形を、同じ二つの区間の間の実ホモトピーへ戻す。 -/
def homotopyOfBoundaryRestriction {l r : (Δ[1] : SSet.{u}) ⟶ E}
    (h : (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ F = intervalBoundaryFamily l r) :
    SSet.Homotopy l r where
  h := (β_ (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).hom ≫ F
  h₀ := by
    change leftSide ≫ F = l
    exact (sides_of_boundary_restriction F h).1
  h₁ := by
    change rightSide ≫ F = r
    exact (sides_of_boundary_restriction F h).2
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

end SerrePositivity.KST.Spectra.SquareAdjustment
