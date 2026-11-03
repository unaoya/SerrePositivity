module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.Slice
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.ElementsDiagram
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafInfinity
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafUnstraightening
public import SerrePositivity.InfinityCategories.F1.Yoneda.YonedaInfinityConstruction
public import SerrePositivity.InfinityCategories.F1.Ind.YonedaSlice

/-!
概要：小さい元の圏から同じ Yoneda slice への底上の比較を、F を頂点とする余錐へ戻す。
方針：同じ slice の普遍族を比較写像で制限し、全図式を保って uncurry する。
規約：比較写像の存在と余極限性は別工程。入力された元の比較を選び直さない。
使われ方：F2N-2(a) の小さい生成図式の密度余錐。
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
  (k : (SSet.uliftFunctor.{u + 1, u}).obj (smallRightUnstraightening F) ⟶ presheafYonedaSlice F)
  (hk : k ≫ presheafYonedaSliceProjection F =
    (SSet.uliftFunctor.{u + 1, u}).map (smallRightUnstraighteningProjection F))

/-- 指定された同じ底上の比較から、元の小さい Yoneda 図式上の全余錐を回収する。 -/
def presheafElementsCoconeOfComparison : JoinCocone (presheafElementsYonedaDiagram F) :=
  ⟨sliceOverUncurry (k ≫ pullback.fst
    (sliceOverProjection (SSet.yonedaEquiv.symm (functorVertex F))) (yonedaInfinityMap C)), by
      rw [sliceOverUncurry_projection, Category.assoc, pullback.condition]
      change k ≫ (presheafYonedaSliceProjection F ≫ yonedaInfinityMap C) = _
      rw [← Category.assoc, hk]
      rfl⟩

/-- 回収した同じ小さい生成図式の全余錐は、元の F 自体を指定頂点に持つ。 -/
lemma presheafElementsCoconeOfComparison_vertex :
    (presheafElementsCoconeOfComparison F k hk).vertex = functorVertex F := by
  rw [JoinCocone.vertex_eq]
  change SSet.yonedaEquiv (_ ≫ sliceOverUncurry _) = _
  rw [sliceOverUncurry_fixed]
  exact SSet.yonedaEquiv.apply_symm_apply _

end SerrePositivity.InfinityCategories.F2.Ind
