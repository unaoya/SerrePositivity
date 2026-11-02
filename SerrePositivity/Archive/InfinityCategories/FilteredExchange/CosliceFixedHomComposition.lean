module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CosliceOppositeHomComposition
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.OppositeHomFixedPostcomposition

/-!
概要：元の固定射による coslice 始点前合成を、全反転 Hom 上の元の後合成へ戻す。
方針：二つの全 Hom の合成則を、元の固定射の係数に制限する。
規約：元の射と全係数の指定値を保持。使われ方：pointed 三角形の頂点値の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 固定した元の射の全退化を前合成すると、全反転 Hom の同じ後合成を回収する。 -/
lemma coherentCosliceSourcePrecomposition_fixed (x : C) {z y : C} (f : z ⟶ y) :
    lift (SSet.const
      ((coherentCosliceFiberComparison z y ≫ vertexFiberι
        (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex z)))
          (coherentNerveVertex y)).app (Opposite.op ⦋0⦌)
            (ULift.up (SSet.opObjEquiv.symm (SimplicialCategory.homEquiv' z y f)))))
      (𝟙 ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x z).op)) ≫
        coherentCosliceSourcePrecomposition x z =
    (SSet.uliftFunctor.{v, u}).map (SSet.opFunctor.map (eHomWhiskerLeft SSet x f)) ≫
      coherentCosliceFiberComparison x y ≫ vertexFiberι
        (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
          (coherentNerveVertex y) := by
  let F : Discrete PUnit.{u + 1} ⥤ C := (Functor.const _).obj y
  let P : (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x z).op ⟶
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom z y).op ⊗
        (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x z).op := lift (SSet.const
    (ULift.up (SSet.opObjEquiv.symm (SimplicialCategory.homEquiv' z y f))))
      (𝟙 ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x z).op))
  have h := congrArg (fun m => P ≫ m)
    (coherentCosliceSourcePrecomposition_hom F x z ⟨PUnit.unit⟩)
  have hu : P ≫ (uliftTensorIso (SimplicialCategory.sHom z y).op
      (SimplicialCategory.sHom x z).op).inv =
    (SSet.uliftFunctor.{v, u}).map
      (lift (SSet.const (SSet.opObjEquiv.symm (SimplicialCategory.homEquiv' z y f)))
        (𝟙 (SimplicialCategory.sHom x z).op)) := rfl
  change P ≫ ((coherentCosliceFiberComparison z y ≫ vertexFiberι _ _) ▷ _) ≫
      coherentCosliceSourcePrecomposition x z =
    P ≫ (uliftTensorIso _ _).inv ≫
      (SSet.uliftFunctor.{v, u}).map (oppositeHomPrecomposition x z y) ≫
        coherentCosliceFiberComparison x y ≫ vertexFiberι _ _ at h
  have hl : P ≫ ((coherentCosliceFiberComparison z y ≫ vertexFiberι
      (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex z)))
        (coherentNerveVertex y)) ▷ _) =
      lift (SSet.const ((coherentCosliceFiberComparison z y ≫ vertexFiberι
        (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex z)))
          (coherentNerveVertex y)).app (Opposite.op ⦋0⦌)
            (ULift.up (SSet.opObjEquiv.symm (SimplicialCategory.homEquiv' z y f)))))
        (𝟙 ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x z).op)) := by
    dsimp only [P]
    rw [lift_whiskerRight, SSet.const_comp]
  simp only [← Category.assoc] at h
  rw [hl, hu] at h
  simp only [Category.assoc] at h
  rw [← Functor.map_comp_assoc, oppositeHomPrecomposition_fixed] at h
  exact h

end SerrePositivity.InfinityCategories.F2
