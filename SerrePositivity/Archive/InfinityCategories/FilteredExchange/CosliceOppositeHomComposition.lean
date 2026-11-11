module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.OppositeHomPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceSourceWeighted
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CosliceTransport

/-!
概要：coslice 全体の始点前合成を、元の二つの全反転 Hom の豊穣合成へ厳密に戻す。
方針：既存の weighted な比較との一致に、定値係数の全 Hom 合成則を適用する。
規約：始点・終点・全係数を保持。使われ方：全 pointed 族の三頂点の元の作用の計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 元の標準 Hom 比較への始点前合成は、元の全反転 Hom の同じ合成を厳密に表す。 -/
lemma coherentCosliceSourcePrecomposition_hom {I : Type u} [SmallCategory I]
    (F : I ⥤ C) (x z : C) (i : I) :
    ((coherentCosliceFiberComparison z (F.obj i) ≫
      vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex z)))
        (coherentNerveVertex (F.obj i))) ▷
          (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x z).op) ≫
      coherentCosliceSourcePrecomposition x z =
    (uliftTensorIso (SimplicialCategory.sHom z (F.obj i)).op
      (SimplicialCategory.sHom x z).op).inv ≫
      (SSet.uliftFunctor.{v, u}).map (oppositeHomPrecomposition x z (F.obj i)) ≫
        coherentCosliceFiberComparison x (F.obj i) ≫
          vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
            (coherentNerveVertex (F.obj i)) := by
  rw [coherentCosliceFiberComparison_weighted_ι F z i, comp_whiskerRight,
    Category.assoc, coherentCosliceSourcePrecomposition_weighted,
    coherentCosliceFiberComparison_weighted_ι F x i]
  unfold weightedCoslicePrecompositionFamily
  have hu :
      ((SSet.uliftFunctor.{v, u}).map
        (weightedNerveConstantLift (simplicialHomDiagram F z ⋙ SSet.opFunctor) i) ▷
          (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x z).op) ≫
        (uliftTensorIso _ _).inv =
      (uliftTensorIso _ _).inv ≫ (SSet.uliftFunctor.{v, u}).map
        (weightedNerveConstantLift (simplicialHomDiagram F z ⋙ SSet.opFunctor) i ▷
          (SimplicialCategory.sHom x z).op) := rfl
  rw [← Category.assoc, hu, Category.assoc, ← Functor.map_comp_assoc,
    weightedConePrecompositionMap_constant, Functor.map_comp]
  simp only [Category.assoc]
  rfl

end SerrePositivity.InfinityCategories.F2
