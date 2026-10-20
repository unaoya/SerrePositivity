module

public import SerrePositivity.KST.Spectra.ExponentialInitialRelativeComposition
public import SerrePositivity.KST.Spectra.SquareBoundaryFamilies

/-!
概要：前半の左右境界が定数なら、後半の非定値な左右境界を全区間で保って貼り合わせる。
方針：前半の全境界射影が定数であることを照合し、後半の左単位三角形を相対充填する。
規約：元の二正方形と実合成三角形を保持。使われ方：交換自然性と入力比較の貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.SquareAdjustment
variable {E : SSet.{u}} {f g k : (Δ[1] : SSet.{u}) ⟶ E}
  (H : SSet.Homotopy f g) (V : SSet.Homotopy g k)

/-- 左右全境界が定数なら、境界全体の射影も元の終辺の制限で一定。 -/
lemma boundary_constant_of_sides (x y : E _⦋0⦌)
    (hL : leftSide ≫ H.h = SSet.const x) (hR : rightSide ≫ H.h = SSet.const y) :
    (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ H.h =
      fst (∂Δ[1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (boundary 1).ι ≫ g := by
  have hl : stdSimplex.δ (1 : Fin 2) ≫ g = SSet.const x := by
    have hc : stdSimplex.δ (1 : Fin 2) ≫ (SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ _) =
        stdSimplex.δ (0 : Fin 2) ≫ leftSide := by
      rw [stdSimplex.δ_one_eq_const, stdSimplex.δ_zero_eq_const]
      ext m s <;> rfl
    rw [← H.h₁, ← Category.assoc, hc, Category.assoc, hL, SSet.comp_const]
  have hr : stdSimplex.δ (0 : Fin 2) ≫ g = SSet.const y := by
    have hc : stdSimplex.δ (0 : Fin 2) ≫ (SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ _) =
        stdSimplex.δ (0 : Fin 2) ≫ rightSide := by
      rw [stdSimplex.δ_zero_eq_const]
      ext m s <;> rfl
    rw [← H.h₁, ← Category.assoc, hc, Category.assoc, hR, SSet.comp_const]
  apply boundary_tensor_hom_ext
  intro j
  simp only [← comp_whiskerRight_assoc, boundary.ι_ι, whiskerRight_fst_assoc]
  fin_cases j
  · change stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u}) ≫ H.h = _
    rw [boundary.ι_ι_assoc, face_right, Category.assoc, hR]
    change snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ SSet.const y =
      fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (stdSimplex.δ (0 : Fin 2) ≫ g)
    rw [hr, SSet.comp_const, SSet.comp_const]
  · change stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u}) ≫ H.h = _
    rw [boundary.ι_ι_assoc, face_left, Category.assoc, hL]
    change snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ SSet.const x =
      fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (stdSimplex.δ (1 : Fin 2) ≫ g)
    rw [hl, SSet.comp_const, SSet.comp_const]

/-- 後半の境界辺の左単位三角形を保持する、元の二正方形の相対合成。 -/
abbrev InitialBoundaryPasting :=
  ExponentialPaths.InitialRelativeComposite (boundary 1).ι H V

/-- 前半の左右境界が定数なら、後半の全境界を変えずに二正方形を合成する。 -/
def InitialBoundaryPasting.choose [KanComplex E] (x y : E _⦋0⦌)
    (hL : leftSide ≫ H.h = SSet.const x) (hR : rightSide ≫ H.h = SSet.const y) :
    InitialBoundaryPasting H V :=
  ExponentialPaths.InitialRelativeComposite.choose (boundary 1).ι H V
    (boundary_constant_of_sides H x y hL hR)

/-- 合成正方形の左辺は後半の元の非定値な辺全体。 -/
lemma InitialBoundaryPasting.left (C : InitialBoundaryPasting H V) :
    leftSide ≫ C.homotopy.h = leftSide ≫ V.h :=
  (sides_eq_of_boundary_eq
    (ExponentialPaths.InitialRelativeComposite.restriction (boundary 1).ι H V C)).1

/-- 合成正方形の右辺も後半の元の非定値な辺全体。 -/
lemma InitialBoundaryPasting.right (C : InitialBoundaryPasting H V) :
    rightSide ≫ C.homotopy.h = rightSide ≫ V.h :=
  (sides_eq_of_boundary_eq
    (ExponentialPaths.InitialRelativeComposite.restriction (boundary 1).ι H V C)).2

end SerrePositivity.KST.Spectra.SquareAdjustment
