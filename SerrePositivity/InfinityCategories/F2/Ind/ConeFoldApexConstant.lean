module

public import SerrePositivity.InfinityCategories.F2.Ind.ArrowInterpolationTipTriangle

/-!
概要：元の余錐点へ定値な旧族は、二重余錐の同じ右二点の折り畳み後も定値。
方針：元の余錐点の右包含で因子化し、零次標準単体への写像の一意性を使う。
規約：元の余錐点と全次数を保持する。
使われ方：元の補間領域の余錐を、全余錐積の同じ終点面として回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：元の余錐点へ定値な旧族は、同じ余錐の折り畳みで定値のまま保たれる。
方針：元の右包含と零次標準単体への一意な写像。規約：全射の等号。使われ方：終点面。 -/
lemma arrowInterpolationConeFold_apex_constant (A L : SSet.{u}) :
    joinMap (SSet.const (SSet.yonedaEquiv (joinInr L (Δ[0] : SSet.{u}))) :
      A ⟶ join L Δ[0]) (𝟙 Δ[0]) ≫ arrowInterpolationConeFold L =
    (SSet.const (SSet.yonedaEquiv (joinInr L (Δ[0] : SSet.{u}))) : join A Δ[0] ⟶ join L Δ[0]) := by
  let t : A ⟶ (Δ[0] : SSet.{u}) := SSet.const (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))
  have hc : (SSet.const (SSet.yonedaEquiv (joinInr L (Δ[0] : SSet.{u}))) : A ⟶ join L Δ[0]) =
      t ≫ joinInr L Δ[0] := by
    dsimp only [t]
    rw [SSet.const_comp]
    rfl
  have hj := joinMap_comp t (joinInr L (Δ[0] : SSet.{u}))
    (𝟙 (Δ[0] : SSet.{u})) (𝟙 Δ[0])
  simp only [Category.id_comp] at hj
  rw [hc, hj, Category.assoc, arrowInterpolationConeFold_rightPair, ← Category.assoc]
  have he : joinMap t (𝟙 (Δ[0] : SSet.{u})) ≫ stableLastJoinEvaluation 0 =
      (SSet.const (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) : join A Δ[0] ⟶ Δ[0]) :=
    stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [he, SSet.const_comp]
  rfl
end SerrePositivity.InfinityCategories.F2.Ind
