module
public import SerrePositivity.InfinityCategories.Stable.ZeroCornerPasting
public import SerrePositivity.InfinityCategories.Stable.SuspensionSquare
/-!
概要：IsStable の fiber・cofiber と零角判定から、任意の二辺の実押し出しを構成する。
方針：第二辺の fiber 列を第一辺に沿って貼り合わせ、外側 cofiber の普遍性を右面へ戻す。
規約：入力の両辺を厳密に保持し、有限極限・余極限を仮定しない。
使われ方：D-7′。任意 span の余極限と有限余極限の一般導出。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

lemma IsStable.exists_pushoutSquare_of_edges {X : SSet.{u}} [Quasicategory X] [IsStable X]
    {x y z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (g : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) :
    ∃ R : Δ[1] ⊗ Δ[1] ⟶ X, IsPushoutSquare R ∧
      squareBottomEdge ≫ R = SSet.yonedaEquiv.symm f.edge ∧
      squareLeftEdge ≫ R = SSet.yonedaEquiv.symm g.edge := by
  let t := chosenFiberSquare g
  have hx : squareVertex t.square 1 0 = x := by
    rw [← squareRightEdge_source, t.right_edge]
    exact (congrArg (X.δ 1)
      ((SSet.yonedaEquiv (X := X) (n := ⦋1⦌)).apply_symm_apply g.edge)).trans g.src_eq
  let f' : SSet.Truncated.Edge (X := (truncation 2).obj X) (squareVertex t.square 1 0) y :=
    ⟨f.edge, f.src_eq.trans hx.symm, f.tgt_eq⟩
  let c := (squareBottomArrow t.square).compStruct f'
  let τ : Δ[2] ⟶ X := SSet.yonedaEquiv.symm c.simplex
  have hface (i : Fin 3) : SSet.yonedaEquiv (stdSimplex.δ i ≫ τ) = X.δ i c.simplex := by
    rw [stdSimplex.yonedaEquiv_δ_comp]
    exact congrArg (X.δ i) (SSet.yonedaEquiv.apply_symm_apply c.simplex)
  have hfirst : squareBottomEdge ≫ t.square = stdSimplex.δ (2 : Fin 3) ≫ τ := by
    apply SSet.yonedaEquiv.injective
    exact ((squareBottomArrow_edge t.square).symm.trans c.d₂.symm).trans (hface 2).symm
  obtain ⟨F, hleft, hbottom, hright, _⟩ := exists_pushoutRectangle_of_zeroTriangle
    t.toZeroTriangle (IsStable.pushout_of_pullback t.toZeroTriangle t.isPullback) τ hfirst
  refine ⟨pastingSquare F 0, hright, ?_, ?_⟩
  · rw [pastingSquare_bottomEdge, hbottom]
    apply SSet.yonedaEquiv.injective
    exact (hface 0).trans (c.d₀.trans (SSet.yonedaEquiv.apply_symm_apply f.edge).symm)
  · rw [← pastingSquare_sharedEdge, hleft]
    exact t.right_edge

lemma IsStable.hasColimit_span {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (p : (horn 2 0 : SSet.{u}) ⟶ X) : HasColimit p := by
  let a := SSet.yonedaEquiv (horn₂₀.ι₀₁ ≫ p)
  let b := SSet.yonedaEquiv (horn₂₀.ι₀₂ ≫ p)
  have hs : X.δ 1 a = X.δ 1 b := by
    change X.δ 1 (SSet.yonedaEquiv (horn₂₀.ι₀₁ ≫ p)) =
      X.δ 1 (SSet.yonedaEquiv (horn₂₀.ι₀₂ ≫ p))
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← stdSimplex.yonedaEquiv_δ_comp,
      ← Category.assoc, ← Category.assoc]
    exact congrArg (fun q => SSet.yonedaEquiv (q ≫ p)) horn₂₀.isPushout.w
  let f : SSet.Truncated.Edge (X := (truncation 2).obj X) (X.δ 1 a) (X.δ 0 a) :=
    ⟨a, rfl, rfl⟩
  let g : SSet.Truncated.Edge (X := (truncation 2).obj X) (X.δ 1 a) (X.δ 0 b) :=
    ⟨b, hs.symm, rfl⟩
  obtain ⟨R, hR, hfirst, hsecond⟩ := IsStable.exists_pushoutSquare_of_edges f g
  have hp : pushoutSpan R = p := by
    apply horn₂₀.isPushout.hom_ext
    · rw [pushoutSpan, ← Category.assoc, spanSquareBoundary_bottomEdge, hfirst]
      exact SSet.yonedaEquiv.symm_apply_apply _
    · rw [pushoutSpan, ← Category.assoc, spanSquareBoundary_leftEdge, hsecond]
      exact SSet.yonedaEquiv.symm_apply_apply _
  rw [← hp]
  exact ⟨pushoutCocone R, hR⟩

end SerrePositivity.InfinityCategories
