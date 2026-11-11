module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedConePrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveFiber

/-!
概要：全反転 Hom の前合成を、weighted nerve の定値係数で厳密に計算する。
方針：元の豊穣合成を反転し、同じ初区間の二係数の制限を Yoneda の自然性でまとめる。
規約：反転を外した右 Hom と同一視しない。使われ方：三辺の実 pointed 値の計算。
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

/-- 元の二つの反転 Hom を、順序を明示した同じ豊穣前合成で結ぶ。 -/
def oppositeHomPrecomposition (x z y : C) :
    (SimplicialCategory.sHom z y).op ⊗ (SimplicialCategory.sHom x z).op ⟶
      (SimplicialCategory.sHom x y).op :=
  (Functor.Monoidal.μIso SSet.opFunctor _ _).hom ≫
    SSet.opFunctor.map ((β_ (SimplicialCategory.sHom z y)
      (SimplicialCategory.sHom x z)).hom ≫ eComp SSet x z y)

/-- 元の weighted な前合成は、同じ定値底の全反転 Hom の合成を厳密に回収する。 -/
lemma weightedConePrecompositionMap_constant {I : Type u} [SmallCategory I]
    (F : I ⥤ C) (x z : C) (i : I) :
    (weightedNerveConstantLift (simplicialHomDiagram F z ⋙ SSet.opFunctor) i ▷
      (SimplicialCategory.sHom x z).op) ≫ weightedConePrecompositionMap F x z =
    oppositeHomPrecomposition x z (F.obj i) ≫
      weightedNerveConstantLift (simplicialHomDiagram F x ⋙ SSet.opFunctor) i := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨a, c⟩
  refine Sigma.ext rfl (heq_of_eq ?_)
  apply NatTrans.ext
  funext j
  change lift
      (stdSimplex.map (simplexPrefixInclusion j.val n _) ≫ SSet.yonedaEquiv.symm a)
      (stdSimplex.map (simplexPrefixInclusion j.val n _) ≫ SSet.yonedaEquiv.symm c) ≫
        oppositeHomPrecomposition x z (F.obj i) =
    stdSimplex.map (simplexPrefixInclusion j.val n _) ≫ SSet.yonedaEquiv.symm
      ((oppositeHomPrecomposition x z (F.obj i)).app (Opposite.op ⦋n⦌) (a, c))
  rw [← comp_lift, Category.assoc]
  change stdSimplex.map (simplexPrefixInclusion j.val n _) ≫
    (SSet.yonedaEquiv.symm (a, c) ≫ oppositeHomPrecomposition x z (F.obj i)) = _
  rw [SSet.yonedaEquiv_symm_comp]

end SerrePositivity.InfinityCategories.F2
