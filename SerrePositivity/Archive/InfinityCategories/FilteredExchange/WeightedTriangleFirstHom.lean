module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.WeightedConstantFiber

/-!
概要：反転した一単体の標準 weighted cone の最初の Hom は元の係数の終点。
方針：反転係数と初区間の座標を全次数で計算する。
規約：元の一単体と全係数を保持し、Kan 性を仮定しない。
使われ方：実終点円柱の最初の辺と標準 Hom 比較の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 標準の反転係数の最初の Hom は元の係数の終点への定値評価。 -/
lemma weightedTriangleFirstHom
    {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (F : I ⥤ C) (x : C) (i : I)
    (s : (SimplicialCategory.sHom x (F.obj i)) _⦋1⦌) :
    weightedConeHom F x
      (weightedNerveConstantDiagram (simplicialHomDiagram F x ⋙ SSet.opFunctor)
        i (SSet.opObjEquiv.symm s)) 0 1 =
      nerveMap ((Functor.const (Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3))
        (ULift.up 1))).obj (ULift.up (1 : Fin 2))) ≫
        (stdSimplex.isoNerve 1).inv ≫ SSet.yonedaEquiv.symm s := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro P
  change (SimplicialCategory.sHom x (F.obj i)).map _ s =
    (SimplicialCategory.sHom x (F.obj i)).map _ s
  apply congrArg (fun a : ⦋d⦌ ⟶ ⦋1⦌ ↦
    (SimplicialCategory.sHom x (F.obj i)).map a.op s)
  ext k
  change 2 - ((_ : Fin 1).val + 1) = 1
  simp only [Fin.eq_zero, Fin.val_zero]

end SerrePositivity.InfinityCategories.F2
