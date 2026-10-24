module

public import SerrePositivity.InfinityCategories.F2.Ind.PointSliceIdentity
public import SerrePositivity.InfinityCategories.F2.Ind.ConeTerminalSliceSection
public import SerrePositivity.InfinityCategories.F2.Ind.JoinAssociatorRightPair

/-!
概要：元の右余錐図式の標準 slice 切断の終点は同じ恒等頂点。
方針：二重余錐の右二点の折り畳みを計算し、元の全余錐を照合する。
規約：元の点写像と全切断を選び直さない。
使われ方：旧族の全円柱を固定する相対余錐延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：元の右余錐図式の標準 slice 切断の終点は同じ恒等頂点。
方針：二重余錐の右二点の折り畳みを計算し、元の全余錐を照合する。
規約：元の全射を保持。使われ方：終点を固定する相対再構成。 -/
lemma coneTerminalSliceSection_tip {L X : SSet.{u}}
    (d : join L (Δ[0] : SSet.{u}) ⟶ X) :
    SSet.yonedaEquiv (joinInr L (Δ[0] : SSet.{u}) ≫ coneTerminalSliceSection d) =
      pointSliceIdentity (joinInr L Δ[0] ≫ d) := by
  apply Subtype.ext
  change (SSet.yonedaEquiv (joinInr L (Δ[0] : SSet.{u}) ≫ coneTerminalSliceSection d)).val =
    SSet.const (SSet.yonedaEquiv (joinInr L Δ[0] ≫ d))
  calc
    _ = sliceOverUncurry (joinInr L (Δ[0] : SSet.{u}) ≫ coneTerminalSliceSection d) := by
      simpa only [Equiv.symm_apply_apply] using
        (sliceOverUncurry_yoneda 0 (SSet.yonedaEquiv
          (joinInr L (Δ[0] : SSet.{u}) ≫ coneTerminalSliceSection d))).symm
    _ = _ := by
      rw [sliceOverUncurry_precomp, coneTerminalSliceSection_uncurry,
        arrowInterpolationConeFold]
      simp only [← Category.assoc]
      rw [joinAssociator_rightPair, joinInr_joinMap, Category.assoc]
      have he : stableLastJoinEvaluation.{u} 0 =
          SSet.const (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) :=
        stdSimplex.isTerminalObj₀.hom_ext _ _
      rw [he, SSet.const_comp]
      rfl
/-- 概要：元の右余錐図式の標準 slice 切断の終点は同じ恒等頂点。
方針：二重余錐の右二点の折り畳みを計算し、元の全余錐を照合する。
規約：元の全射を保持。使われ方：終点を固定する相対再構成。 -/
lemma coneTerminalSliceSection_tip_isTerminal {L X : SSet.{u}} [Quasicategory X]
    (d : join L (Δ[0] : SSet.{u}) ⟶ X) :
    IsTerminalVertex (SSet.yonedaEquiv
      (joinInr L (Δ[0] : SSet.{u}) ≫ coneTerminalSliceSection d)) := by
  rw [coneTerminalSliceSection_tip]
  exact pointSliceIdentity_isTerminal _

end SerrePositivity.InfinityCategories.F2.Ind
