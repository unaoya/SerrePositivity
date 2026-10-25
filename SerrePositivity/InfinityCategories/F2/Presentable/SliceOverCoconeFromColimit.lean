module

public import SerrePositivity.InfinityCategories.F2.Presentable.IteratedCoconeReassociation
public import SerrePositivity.InfinityCategories.Core.InitialTransport
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct

/-!
概要：元の対象の上の図式に、底の指定余極限を射影とする余錐を構成する。
方針：余極限余錐から元の増大余錐への辺を選び、二重 join を組み替える。
規約：元の対象への全図式と底の全余極限余錐を厳密に保持する。
使われ方：compact 候補の対象上の comma における filtered 性の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：slice 内の図式に、指定した底の余極限余錐を持つ余錐が存在する。
方針：余錐圏内の始対象から増大余錐への辺を二重余錐として読む。
規約：底の余極限余錐を選び直さず、その全射を回収する。
使われ方：対象上の compact 図式へ compact な余錐を付ける。 -/
lemma exists_sliceOver_cocone_lifting_colimit {K X : SSet.{u}}
    (x : (Δ[0] : SSet.{u}) ⟶ X) (a : K ⟶ sliceOver x)
    (c : JoinCocone (a ≫ sliceOverProjection x)) (hc : IsColimitCone c) :
    ∃ d : JoinCocone a, d.val ≫ sliceOverProjection x = c.val := by
  let b : JoinCocone (a ≫ sliceOverProjection x) :=
    ⟨sliceOverUncurry a, sliceOverUncurry_projection a⟩
  obtain ⟨e₀⟩ := hc.nonempty_edge b
  let e := SSet.Edge.ofTruncated (X := sliceUnder (a ≫ sliceOverProjection x)) e₀
  let U := sliceUnderUncurry (SSet.yonedaEquiv.symm e.edge)
  have hU₀ : joinMap (𝟙 K) (SSet.stdSimplex.δ (1 : Fin 2)) ≫ U = c.val := by
    dsimp only [U]
    rw [← sliceUnderUncurry_precomp, e.δ_one_yonedaEquiv_symm,
      sliceUnderUncurry_yoneda]
  have hU₁ : joinMap (𝟙 K) (SSet.stdSimplex.δ (0 : Fin 2)) ≫ U = b.val := by
    dsimp only [U]
    rw [← sliceUnderUncurry_precomp, e.δ_zero_yonedaEquiv_symm,
      sliceUnderUncurry_yoneda]
  let G := iteratedCoconeReassociation K ≫ U
  have hG : joinInr (join K Δ[0]) Δ[0] ≫ G = x := by
    calc
      _ = (SSet.stdSimplex.δ (0 : Fin 2) ≫ joinInr K Δ[1]) ≫ U := by
        dsimp only [G]
        rw [← Category.assoc, iteratedCoconeReassociation_inr]
      _ = (joinInr K Δ[0] ≫ joinMap (𝟙 K) (SSet.stdSimplex.δ (0 : Fin 2))) ≫ U := by
        rw [joinInr_joinMap]
      _ = joinInr K Δ[0] ≫ b.val := by rw [Category.assoc, hU₁]
      _ = x := sliceOverUncurry_fixed a
  let d := sliceOverCurry G hG
  have hd : joinInl K Δ[0] ≫ d = a := by
    apply sliceOverUncurry_injective x
    rw [sliceOverUncurry_precomp]
    dsimp only [d]
    rw [sliceOverUncurry_curry]
    dsimp only [G]
    rw [← Category.assoc, iteratedCoconeReassociation_middle, hU₁]
  refine ⟨⟨d, hd⟩, ?_⟩
  dsimp only [d]
  rw [sliceOverCurry_projection]
  dsimp only [G]
  rw [← Category.assoc, iteratedCoconeReassociation_inl, hU₀]

end SerrePositivity.InfinityCategories.F2.Presentable
