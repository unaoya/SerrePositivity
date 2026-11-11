module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.WeightedConstantFiber

/-!
概要：反転した一単体から作る標準 weighted cone の長辺 Hom を計算する。
方針：反転 Yoneda 射の公式で二つの反転を消去する。
規約：元の係数と全次数を保持し、Kan 性を仮定しない。
使われ方：実終点円柱と標準 Hom 比較の長辺の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 標準の反転係数の長辺 Hom は元の係数を反転最小点で評価する射。 -/
lemma weightedTriangleLongHom
    {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (F : I ⥤ C) (x : C) (i : I)
    (s : (SimplicialCategory.sHom x (F.obj i)) _⦋1⦌) :
    weightedConeHom F x
      (weightedNerveConstantDiagram (simplicialHomDiagram F x ⋙ SSet.opFunctor)
        i (SSet.opObjEquiv.symm s)) 0 2 =
      nerveMap (pathFirstMinimumReverseFunctor (1 : Fin 2)) ≫
        (stdSimplex.isoNerve 1).inv ≫ SSet.yonedaEquiv.symm s := by
  change pathFirstMinimumMap (1 : Fin 2) ≫
    reflectedSimplexMap (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm s)) = _
  rw [reflectedYonedaMap]
  change (nerveMap (pathFirstMinimumReverseFunctor (1 : Fin 2)) ≫
    (stdSimplex.isoNerve 1).inv ≫ (stdSimplex.opIso ⦋1⦌).inv) ≫
      ((stdSimplex.opIso ⦋1⦌).hom ≫ SSet.yonedaEquiv.symm
        (SSet.opObjEquiv (SSet.opObjEquiv.symm s))) = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.F2
