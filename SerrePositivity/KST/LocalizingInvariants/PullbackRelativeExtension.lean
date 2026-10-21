module

public import SerrePositivity.KST.LocalizingInvariants.PullbackTerminalBoundary
public import SerrePositivity.InfinityCategories.Core.RelativeTerminalExtension

/-!
概要：指定部分の外の単体の最終頂点で普遍的な正方形族は、cospan の上で相対延長する。
方針：各終点の pullback 性を終点境界充填に移し、相対骨格を埋める。
規約：全 pullback の存在や安定性は要求しない。使われ方：cartesian 辺の外ホーンの充填。
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

lemma exists_relative_squareFamily_of_pullback_last_vertices
    {B X : SSet.{u}} [Quasicategory X] (A : B.Subcomplex)
    (hA : ∀ v : B _⦋0⦌, v ∈ A.obj (Opposite.op ⦋0⦌))
    (a : (A : SSet.{u}) ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X)
    (b : B ⟶ (ihom (horn 2 2 : SSet.{u})).obj X)
    (ha : a ≫ (pre cospanSquareBoundary).app X = A.ι ≫ b)
    (ht : ∀ (n : ℕ) (s : B _⦋n + 1⦌), s ∉ A.obj (Opposite.op ⦋n + 1⦌) →
      IsPullbackSquare ((functorVertexEquiv (Δ[1] ⊗ Δ[1] : SSet.{u}) X).symm
        (a.app (Opposite.op ⦋0⦌) ⟨simplexLastVertex s, hA _⟩))) :
    ∃ F : B ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X,
      A.ι ≫ F = a ∧ F ≫ (pre cospanSquareBoundary).app X = b := by
  apply exists_lift_of_terminal_last_vertices A hA _ a b ha
  intro n s hs
  let v := a.app (Opposite.op ⦋0⦌) ⟨simplexLastVertex s, hA _⟩
  let R := (functorVertexEquiv (Δ[1] ⊗ Δ[1] : SSet.{u}) X).symm v
  have hR : IsPullbackSquare R := ht n s hs
  have h := pullbackSquare_terminalBoundaryLifting R hR
  have hv : functorVertex R = v := (functorVertexEquiv _ _).apply_symm_apply v
  exact (congrArg (TerminalBoundaryLifting ((pre cospanSquareBoundary).app X)) hv).mp h

end SerrePositivity.KST.LocalizingInvariants
