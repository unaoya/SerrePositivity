module

public import SerrePositivity.KST.LocalizingInvariants.IdentityArrowPullback
public import SerrePositivity.InfinityCategories.Stable.SquareHorizontalHomotopies
public import SerrePositivity.InfinityCategories.F1.SquareFunctorTransport
public import SerrePositivity.InfinityCategories.Stable.PastingSplitProjection

/-!
概要：上下の辺が可逆な実正方形は pullback である。
方針：水平方向の変形を点ごとに可逆と示し、元の右列を複製した正方形へ比較する。
規約：任意の quasicategory での主張。使われ方：graph 長方形の恒等辺を持つ外周。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma squareColumnDiagram_isPullback {X : SSet.{u}} [Quasicategory X]
    (f : (Δ[1] : SSet.{u}) ⟶ X) : IsPullbackSquare (squareColumnDiagram f) := by
  have ht := (isPullbackSquare_iff_transpose _).mp (identityArrowSquare_isPullback f)
  simpa only [squareColumnDiagram, ← Category.assoc, braiding_hom_fst] using ht

lemma horizontalRightHomotopy_invertible {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X)
    (hb : IsInvertibleEdge (squareBottomArrow F)) (ht : IsInvertibleEdge (squareTopArrow F))
    (v : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋0⦌) :
    IsInvertibleEdge
      (simplicialHomotopyVertexEdge (squareHorizontalRightHomotopy F) v).toTruncated := by
  rcases v with ⟨s, t⟩
  obtain ⟨a, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective s
  obtain ⟨b, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective t
  fin_cases a <;> fin_cases b
  · apply (isInvertibleEdge_congr (e := squareBottomArrow F) ?_).mp hb
    rw [squareBottomArrow_edge, SSet.yonedaEquiv_comp]
    apply congrArg (F.app (Opposite.op ⦋1⦌))
    apply Prod.ext <;> apply stdSimplex.ext <;> intro j <;> fin_cases j <;> rfl
  · apply (isInvertibleEdge_congr (e := squareTopArrow F) ?_).mp ht
    rw [squareTopArrow_edge, SSet.yonedaEquiv_comp]
    apply congrArg (F.app (Opposite.op ⦋1⦌))
    apply Prod.ext <;> apply stdSimplex.ext <;> intro j <;> fin_cases j <;> rfl
  · have hi : IsInvertibleEdge (Truncated.Edge.id (X := (truncation 2).obj X)
        (squareVertex F 1 0)) := by
      change IsIso (Truncated.HomotopyCategory.homMk _)
      rw [Truncated.HomotopyCategory.homMk_id]
      infer_instance
    apply (isInvertibleEdge_congr (e := Truncated.Edge.id (squareVertex F 1 0)) ?_).mp hi
    rw [← pinchedConstant_one]
    change PinchedHom.constant (F.app (Opposite.op ⦋0⦌) _) 1 = _
    rw [← pinchedConstant_map]
    apply congrArg (F.app (Opposite.op ⦋1⦌))
    apply Prod.ext <;> apply stdSimplex.ext <;> intro j <;> fin_cases j <;> rfl
  · have hi : IsInvertibleEdge (Truncated.Edge.id (X := (truncation 2).obj X)
        (squareVertex F 1 1)) := by
      change IsIso (Truncated.HomotopyCategory.homMk _)
      rw [Truncated.HomotopyCategory.homMk_id]
      infer_instance
    apply (isInvertibleEdge_congr (e := Truncated.Edge.id (squareVertex F 1 1)) ?_).mp hi
    rw [← pinchedConstant_one]
    change PinchedHom.constant (F.app (Opposite.op ⦋0⦌) _) 1 = _
    rw [← pinchedConstant_map]
    apply congrArg (F.app (Opposite.op ⦋1⦌))
    apply Prod.ext <;> apply stdSimplex.ext <;> intro j <;> fin_cases j <;> rfl

lemma isPullbackSquare_of_horizontal_invertible {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X)
    (hb : IsInvertibleEdge (squareBottomArrow F)) (ht : IsInvertibleEdge (squareTopArrow F)) :
    IsPullbackSquare F := by
  let e := functorIsoOfPointwiseInvertibleHomotopy (squareHorizontalRightHomotopy F)
    (horizontalRightHomotopy_invertible F hb ht)
  exact (squareColumnDiagram_isPullback (squareRightEdge ≫ F)).of_functorIso e.symm

end SerrePositivity.KST.LocalizingInvariants
