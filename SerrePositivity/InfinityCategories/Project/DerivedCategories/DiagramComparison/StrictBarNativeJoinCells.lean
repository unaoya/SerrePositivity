module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarNativeFunctorCocone

/-!
概要：貼り合わせた全 native 余錐族の各セルは、元の同じ native セルの全族である。
方針：既存 slice の curry と uncurry の逆則を全単体で評価する。
規約：join のセルを新たに作り直さない。
使われ方：3b-3 R6、同じ指定余錐と全パラメーターでの比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet MonoidalCategory MonoidalClosed
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (J : Type) [SmallCategory J]

/-- 全余錐族の一つの join セルは、同じ native セル族の curry に一致する。 -/
lemma strictBarNativeFunctorCocone_cell {n : ℕ} (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌) :
    joinMap (SSet.yonedaEquiv.symm (ULift.up s) : (Δ[n] : SSet.{u + 1}) ⟶ ((SSet.uliftFunctor.{u + 1, u}).obj ((SSet.uliftFunctor.{u, 0}).obj (nerve J))))
        (𝟙 Δ[0]) ≫ (strictBarNativeFunctorCocone A J).val =
      (joinStdSimplexIso n 0).hom ≫ curry (strictBarNativeCellEvaluation A J s) := by
  have h := sliceOverCurry_uncurry (strictBarNativeFunctorOverSection A J)
  exact congrArg (fun f => (f.app (Opposite.op ⦋n⦌) (ULift.up s)).val) h

/-- 全パラメーターを残した各 join セルの評価も、元の同じ native セル族に戻る。 -/
lemma strictBarNativeJoinFamily_cell {n : ℕ} (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌) :
    ((nerve (J ⥤ ModuleCategory A PUnit.{1})) ◁ joinMap (SSet.yonedaEquiv.symm (ULift.up s) : (Δ[n] : SSet.{u + 1}) ⟶ ((SSet.uliftFunctor.{u + 1, u}).obj ((SSet.uliftFunctor.{u, 0}).obj (nerve J))))
        (𝟙 Δ[0])) ≫ strictBarNativeJoinFamily A J =
      ((nerve (J ⥤ ModuleCategory A PUnit.{1})) ◁ (joinStdSimplexIso n 0).hom) ≫ strictBarNativeCellEvaluation A J s := by
  rw [strictBarNativeJoinFamily, ← uncurry_natural_left,
    strictBarNativeFunctorCocone_cell, uncurry_natural_left, uncurry_curry]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
