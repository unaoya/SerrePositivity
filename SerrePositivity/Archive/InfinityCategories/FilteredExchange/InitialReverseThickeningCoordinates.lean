module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.WeightedConstantSimplex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeInitialParameter

/-!
概要：実際の thickening の反転射を、既存の初点 path の反転関手に一致させる。
方針：端点の表示変更の後、全ての path の旗で同じ反転頂点集合を比較する。
規約：元の全 path を保持。使われ方：全係数の反転合成 prism の初点 Hom の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 元の実反転射の初点 Hom は、端点を揃えると既存の path 反転の nerve。 -/
lemma coherentReverseThickening_initial_map {n : ℕ} (j : Fin (n + 1)) :
    (coherentReverseThickening (n + 1)).map ⟨ULift.up 0⟩ ⟨ULift.up j.succ⟩ ≫
      eqToHom (congrArg₂
        (fun A B : SimplicialThickening (ULift.{u} (Fin (n + 2))) ↦
          SimplicialCategory.sHom A B)
        (congrArg (fun a ↦ (⟨ULift.up a⟩ :
          SimplicialThickening (ULift.{u} (Fin (n + 2))))) (Fin.rev_succ j))
        (congrArg (fun a ↦ (⟨ULift.up a⟩ :
          SimplicialThickening (ULift.{u} (Fin (n + 2))))) (Fin.rev_zero (n + 1)))) =
      nerveMap (reflectedFirstPathFunctor j) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  apply CategoryTheory.Functor.ext (fun k ↦ ?_)
  apply SimplicialThickening.Path.ext
  change (((eqToHom (congrArg₂
    (fun A B : SimplicialThickening (ULift.{u} (Fin (n + 2))) ↦
      SimplicialCategory.sHom A B)
    (congrArg (fun a ↦ (⟨ULift.up a⟩ :
      SimplicialThickening (ULift.{u} (Fin (n + 2))))) (Fin.rev_succ j))
    (congrArg (fun a ↦ (⟨ULift.up a⟩ :
      SimplicialThickening (ULift.{u} (Fin (n + 2))))) (Fin.rev_zero (n + 1))))).app d
    (((coherentReverseThickening (n + 1)).map
      ⟨ULift.up 0⟩ ⟨ULift.up j.succ⟩).app d P)).obj k).I = _
  rw [thickeningHom_transport_I
    (congrArg (fun a ↦ (⟨ULift.up a⟩ :
      SimplicialThickening (ULift.{u} (Fin (n + 2))))) (Fin.rev_succ j))
    (congrArg (fun a ↦ (⟨ULift.up a⟩ :
      SimplicialThickening (ULift.{u} (Fin (n + 2))))) (Fin.rev_zero (n + 1)))]
  rfl

/-- 初点係数の実評価は反転 path 上の同じ最大座標による評価。 -/
lemma coneInitialParameter_reflected_coefficient {X : SSet.{u}} {n : ℕ}
    (p : X.op _⦋n⦌) (j : Fin (n + 1)) :
    pathFirstParameterMap j ≫ reflectedSimplexMap (SSet.yonedaEquiv.symm p) =
      nerveMap (reflectedFirstPathFunctor j) ≫ pathLastMaximumMap j.rev ≫
        SSet.yonedaEquiv.symm (SSet.opObjEquiv p) := by
  rw [pathFirstParameterMap, Category.assoc, reflectedYonedaMap]
  simpa only [Category.assoc] using congrArg
    (fun t ↦ t ≫ SSet.yonedaEquiv.symm (SSet.opObjEquiv p))
    (reflectedFirstPathMaximumMap j)

end SerrePositivity.InfinityCategories.F2
