module

public import SerrePositivity.InfinityCategories.F1.YonedaInfinityConstruction
public import SerrePositivity.InfinityCategories.Stable.Cocone

/-!
概要：元の前層 F への Yoneda slice と、F 自体を頂点に持つ同じ標準全余錐を構成する。
方針：Yoneda に沿って F の slice を引き戻し、元の slice の普遍族を uncurry する。
規約：この添字は宇宙 u+1。小さい元の圏との比較と余極限性は別工程。
使われ方：F2N-2(a) の密度余錐を指定した頂点で保持する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})

/-- 元の前層 F への Yoneda 射の全体。添字の小ささはまだ主張しない。 -/
def presheafYonedaSlice : SSet.{u + 1} :=
  pullback (sliceOverProjection (SSet.yonedaEquiv.symm (functorVertex F))) (yonedaInfinityMap C)

/-- 同じ Yoneda slice から元の C の宇宙持ち上げへの射影。 -/
def presheafYonedaSliceProjection :
    presheafYonedaSlice F ⟶ (SSet.uliftFunctor.{u + 1, u}).obj C :=
  pullback.snd _ _

/-- 同じ射影は right fibration。 -/
instance presheafYonedaSliceProjection_rightFibration :
    RightFibration (presheafYonedaSliceProjection F) :=
  ⟨rightFibrations.pullback_snd _ _ (RightFibration.mem (p :=
    sliceOverProjection (SSet.yonedaEquiv.symm (functorVertex F))))⟩

/-- 同じ Yoneda slice は quasicategory。 -/
instance presheafYonedaSlice_quasicategory : Quasicategory (presheafYonedaSlice F) :=
  quasicategory_of_innerFibration (presheafYonedaSliceProjection F)

/-- 元の Yoneda slice の射影を同じ Yoneda へ合成した、表現可能前層の図式。 -/
def presheafYonedaSliceDiagram : presheafYonedaSlice F ⟶ PresheafInfinity C :=
  presheafYonedaSliceProjection F ≫ yonedaInfinityMap C

/-- 元の F への全ての Yoneda 射からなる、F 自体を指定頂点とする標準全余錐。 -/
def presheafYonedaSliceCocone : JoinCocone (presheafYonedaSliceDiagram F) :=
  ⟨sliceOverUncurry (pullback.fst
    (sliceOverProjection (SSet.yonedaEquiv.symm (functorVertex F))) (yonedaInfinityMap C)), by
      rw [sliceOverUncurry_projection]
      exact pullback.condition⟩

/-- 標準全余錐の頂点は、同じ元の前層 F そのもの。 -/
lemma presheafYonedaSliceCocone_vertex :
    (presheafYonedaSliceCocone F).vertex = functorVertex F := by
  rw [JoinCocone.vertex_eq]
  change SSet.yonedaEquiv (_ ≫ sliceOverUncurry _) = _
  rw [sliceOverUncurry_fixed]
  exact SSet.yonedaEquiv.apply_symm_apply _

end SerrePositivity.InfinityCategories.F2.Ind
