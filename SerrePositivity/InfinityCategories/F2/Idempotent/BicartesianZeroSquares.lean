module

public import SerrePositivity.InfinityCategories.F2.Idempotent.PullbackRetracts
public import SerrePositivity.InfinityCategories.F2.Idempotent.ZeroRetracts
public import SerrePositivity.InfinityCategories.F2.Idempotent.FunctorComplete
public import SerrePositivity.InfinityCategories.Core.Idempotent.FullSubcomplexSplitting

/-!
概要：冪等完備な元の標的の双カルテジアンな零角四角形の全 ∞ 圏は冪等完備。
方針：全四角形の関手圏内で、零角・引き戻し・押し出しの三条件の retract 閉性を使う。
規約：元の全四角形とその両普遍性を保持。全辺に存在するとはまだ主張しない。
使われ方：辺の冪等完備化から新しい辺の双カルテジアンな cofiber を回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の全四角形が、同じ零角を持ち、引き戻しと押し出しの両方である条件。 -/
def IsBicartesianZeroVertex {X : SSet.{u}}
    (v : ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) _⦋0⦌) : Prop :=
  let F := (functorVertexEquiv ((Δ[1] : SSet.{u}) ⊗ Δ[1]) X).symm v
  IsZeroVertex (squareVertex F 0 1) ∧ IsPullbackSquare F ∧ IsPushoutSquare F

/-- 元の同じ四角形の関手頂点の三条件は、元の零角と両普遍性そのもの。 -/
lemma isBicartesianZeroVertex_functorVertex {X : SSet.{u}}
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    IsBicartesianZeroVertex (functorVertex F) ↔
      IsZeroVertex (squareVertex F 0 1) ∧ IsPullbackSquare F ∧ IsPushoutSquare F := by
  unfold IsBicartesianZeroVertex
  rw [← functorVertexEquiv_apply F, Equiv.symm_apply_apply]

/-- 元の全四角形の関手 ∞ 圏内の retract は、零角と双カルテジアン性を保つ。 -/
lemma isBicartesianZeroVertex_of_retract {X : SSet.{u}} [Quasicategory X]
    {v w : ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) _⦋0⦌}
    (r : IsVertexRetractOf v w) (hw : IsBicartesianZeroVertex w) :
    IsBicartesianZeroVertex v := by
  obtain ⟨F, rfl⟩ := (functorVertexEquiv ((Δ[1] : SSet.{u}) ⊗ Δ[1]) X).surjective v
  obtain ⟨G, rfl⟩ := (functorVertexEquiv ((Δ[1] : SSet.{u}) ⊗ Δ[1]) X).surjective w
  simp only [functorVertexEquiv_apply] at r hw ⊢
  rw [isBicartesianZeroVertex_functorVertex] at hw ⊢
  let z := (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2))
  have rz : VertexRetraction (squareVertex F 0 1) (squareVertex G 0 1) := by
    change VertexRetraction (F.app (Opposite.op ⦋0⦌) z) (G.app (Opposite.op ⦋0⦌) z)
    have h := r.some.map (hoFunctor.map (evaluateFunctorAt (Y := X) z)).toFunctor
    change VertexRetraction
      ((evaluateFunctorAt (Y := X) z).app (Opposite.op ⦋0⦌) (functorVertex F))
      ((evaluateFunctorAt (Y := X) z).app (Opposite.op ⦋0⦌) (functorVertex G)) at h
    simpa only [evaluateFunctorAt_functorVertex] using h
  exact ⟨isZeroVertex_of_vertexRetraction rz hw.1,
    isPullbackSquare_of_diagram_retract F G r.some hw.2.1,
    isPushoutSquare_of_diagram_retract F G r.some hw.2.2⟩

/-- 元の全四角形の中の、双カルテジアンな零角四角形の全部分 ∞ 圏。 -/
def bicartesianZeroSquares (X : SSet.{u}) : SSet.{u} :=
  (fullSubcomplexOnVertices ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)
    IsBicartesianZeroVertex : SSet.{u})

/-- 元の双カルテジアンな零角四角形は、全部分 quasicategory をなす。 -/
instance bicartesianZeroSquares_quasicategory (X : SSet.{u}) [Quasicategory X] :
    Quasicategory (bicartesianZeroSquares X) :=
  fullSubcomplexOnVertices_quasicategory _ _

/-- 元の冪等完備な標的の双カルテジアンな零角四角形の全 ∞ 圏は冪等完備。 -/
lemma bicartesianZeroSquares_isIdempotentComplete {X : SSet.{u}} [Quasicategory X]
    (hX : IsIdempotentComplete X) : IsIdempotentComplete (bicartesianZeroSquares X) :=
  fullSubcomplex_isIdempotentComplete IsBicartesianZeroVertex
    (fun r hw ↦ isBicartesianZeroVertex_of_retract r hw)
    (functor_isIdempotentComplete ((Δ[1] : SSet.{u}) ⊗ Δ[1]) hX)

/-- 元の双カルテジアンな零角四角形を、その元の下辺へ制限する射影。 -/
def bicartesianZeroBottomProjection (X : SSet.{u}) :
    bicartesianZeroSquares X ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  (fullSubcomplexOnVertices _ IsBicartesianZeroVertex).ι ≫ (pre squareBottomEdge).app X

end SerrePositivity.InfinityCategories.F2.Idempotent
