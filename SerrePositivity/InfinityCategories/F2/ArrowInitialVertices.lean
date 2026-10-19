module

public import SerrePositivity.InfinityCategories.F2.ArrowEndpointPair
public import SerrePositivity.InfinityCategories.F1B.FunctorInitial

/-!
概要：両端が始対象である矢印は矢印圏の始対象。
方針：区間の全頂点が二つの端点のいずれかであることを使う。
規約：元の矢印を変えずに点ごとの始対象判定を適用する。
使われ方：lax pullback の三成分による始対象の判定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：両端が始対象である指定矢印は矢印圏の始対象。
方針：元の頂点を区間関手に戻し、各頂点で始対象性を確認する。
規約：標的の quasicategory 性を仮定しない向きの判定。
使われ方：lax pullback の可縮写像空間による始対象性。 -/
lemma isInitialVertex_arrow_of_endpoints {C : SSet.{u}}
    (e : ((ihom (Δ[1] : SSet.{u})).obj C) _⦋0⦌)
    (h0 : IsInitialVertex
      ((evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)).app (Opposite.op ⦋0⦌) e))
    (h1 : IsInitialVertex
      ((evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1)).app (Opposite.op ⦋0⦌) e)) :
    IsInitialVertex e := by
  obtain ⟨f, rfl⟩ := (functorVertexEquiv (Δ[1] : SSet.{u}) C).surjective e
  change IsInitialVertex (functorVertex f)
  apply isInitialVertex_functorVertex_of_pointwise
  intro k
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective k
  fin_cases i
  · simpa only [functorVertexEquiv_apply, evaluateFunctorAt_functorVertex] using! h0
  · simpa only [functorVertexEquiv_apply, evaluateFunctorAt_functorVertex] using! h1

end SerrePositivity.InfinityCategories.F2
