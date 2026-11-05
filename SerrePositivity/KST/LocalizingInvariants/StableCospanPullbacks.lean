module

public import SerrePositivity.InfinityCategories.Stable.StableSpanPushout
public import SerrePositivity.InfinityCategories.Stable.StableOpposite

/-!
概要：安定な quasicategory の任意の指定二辺の cospan に、実普遍 pullback を構成する。
方針：SConstruction の任意 span の押し出しを読み取り専用で使い、二重反対から戻す。
規約：入力の二辺を厳密に保持。使われ方：普遍な Ore 四角形と分母の基底変更。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma dualSquare_topEdge {X : SSet.{u}} (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    squareTopEdge ≫ dualSquare R = reverseSimplex 1 (squareLeftEdge ≫ R) := by
  apply SSet.yonedaEquiv.injective
  rfl

lemma reverse_edgeOp_unop {X : SSet.{u}} {x y : X _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj X) x y) :
    reverseSimplex 1 ((SSet.yonedaEquiv (X := X.op) (n := ⦋1⦌)).symm (edgeOp f).edge) ≫
        (SSet.opFunctorCompOpFunctorIso.app X).hom = SSet.yonedaEquiv.symm f.edge := by
  apply SSet.yonedaEquiv.injective
  change (SSet.yonedaEquiv.symm f.edge).app (Opposite.op ⦋1⦌) _ =
    (SSet.yonedaEquiv.symm f.edge).app (Opposite.op ⦋1⦌) _
  congr 1
  apply stdSimplex.ext
  intro i
  fin_cases i <;> rfl

lemma exists_stable_pullbackSquare_of_edges {X : SSet.{u}} [Quasicategory X] [IsStable X]
    {x y z : X _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj X) x z)
    (g : Truncated.Edge (X := (truncation 2).obj X) y z) :
    ∃ R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X,
      IsPullbackSquare R ∧ squareRightEdge ≫ R = SSet.yonedaEquiv.symm f.edge ∧
        squareTopEdge ≫ R = SSet.yonedaEquiv.symm g.edge := by
  obtain ⟨S, hS, hP⟩ := _root_.SerrePositivity.InfinityCategories.Stable.exists_stable_pushoutSquare_of_span
    (edgeSpan (X := X.op) (edgeOp f) (edgeOp g))
  have hb : squareBottomEdge ≫ S =
      (SSet.yonedaEquiv (X := X.op) (n := ⦋1⦌)).symm (edgeOp f).edge := by
    have h := congrArg (horn₂₀.ι₀₁ ≫ ·) hS
    rw [pushoutSpan, ← Category.assoc, spanSquareBoundary_bottomEdge,
      edgeSpan_left (X := X.op)] at h
    exact h
  have hl : squareLeftEdge ≫ S =
      (SSet.yonedaEquiv (X := X.op) (n := ⦋1⦌)).symm (edgeOp g).edge := by
    have h := congrArg (horn₂₀.ι₀₂ ≫ ·) hS
    rw [pushoutSpan, ← Category.assoc, spanSquareBoundary_leftEdge,
      edgeSpan_right (X := X.op)] at h
    exact h
  let q := (SSet.opFunctorCompOpFunctorIso.app X).hom
  refine ⟨dualSquare S ≫ q, ?_, ?_, ?_⟩
  · exact (isPullbackSquare_iff_postcomp_isIso (dualSquare S) q).mp
      ((isPushoutSquare_iff_dualSquare S).mp hP)
  · rw [← Category.assoc, dualSquare_rightEdge, hb]
    exact reverse_edgeOp_unop f
  · rw [← Category.assoc, dualSquare_topEdge, hl]
    exact reverse_edgeOp_unop g

lemma stable_hasLimit_edgeCospan {X : SSet.{u}} [Quasicategory X] [IsStable X]
    {x y z : X _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj X) x z)
    (g : Truncated.Edge (X := (truncation 2).obj X) y z) : HasLimit (edgeCospan f g) := by
  obtain ⟨R, hR, hr, ht⟩ := exists_stable_pullbackSquare_of_edges f g
  have hc : pullbackCospan R = edgeCospan f g := by
    apply horn₂₂.isPushout.hom_ext
    · rw [pullbackCospan, ← Category.assoc, cospanSquareBoundary_rightEdge, hr, edgeCospan_left]
    · rw [pullbackCospan, ← Category.assoc, cospanSquareBoundary_topEdge, ht, edgeCospan_right]
  rw [← hc]
  exact ⟨pullbackCone R, hR⟩

lemma exists_edgeCospan_presentation {X : SSet.{u}} (p : (horn 2 2 : SSet.{u}) ⟶ X) :
    ∃ (x y z : X _⦋0⦌)
      (f : Truncated.Edge (X := (truncation 2).obj X) x z)
      (g : Truncated.Edge (X := (truncation 2).obj X) y z), edgeCospan f g = p := by
  let f := edgeOfSimplex (SSet.yonedaEquiv (horn₂₂.ι₀₂ ≫ p))
  let t := SSet.yonedaEquiv (horn₂₂.ι₁₂ ≫ p)
  have ht : X.δ 0 t = X.δ 0 f.edge := by
    change X.δ 0 (SSet.yonedaEquiv (horn₂₂.ι₁₂ ≫ p)) =
      X.δ 0 (SSet.yonedaEquiv (horn₂₂.ι₀₂ ≫ p))
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← stdSimplex.yonedaEquiv_δ_comp]
    apply congrArg SSet.yonedaEquiv
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ p) horn₂₂.isPushout.w.symm).trans (Category.assoc _ _ _))
  let g : Truncated.Edge (X := (truncation 2).obj X) (X.δ 1 t) (X.δ 0 f.edge) :=
    ⟨t, rfl, ht⟩
  refine ⟨_, _, _, f, g, ?_⟩
  apply horn₂₂.isPushout.hom_ext
  · rw [edgeCospan_left]
    exact SSet.yonedaEquiv.symm_apply_apply _
  · rw [edgeCospan_right]
    exact SSet.yonedaEquiv.symm_apply_apply _

lemma stable_hasLimit_cospan {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (p : (horn 2 2 : SSet.{u}) ⟶ X) : HasLimit p := by
  obtain ⟨_, _, _, f, g, rfl⟩ := exists_edgeCospan_presentation p
  exact stable_hasLimit_edgeCospan f g

end SerrePositivity.KST.LocalizingInvariants
