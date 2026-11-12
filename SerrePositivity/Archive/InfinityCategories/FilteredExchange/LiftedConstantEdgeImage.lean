module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ConstantSimplexEdge
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InvertibleEdge

/-!
概要：元の定値引き戻しの宇宙持ち上げ後の像も同じ端点像の退化辺。
方針：元の退化辺の式と同じ射の自然性を合成する。
規約：持ち上げた元の端点と反転を保持する。
使われ方：標準 Kan の左右区間族に現れる二つの定値辺を厳密に退化辺へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ持ち上げた定値引き戻しの像は元の持ち上げた端点像の退化辺。 -/
lemma liftedConstantSimplexPullback_image_degenerate {X : SSet.{u}} {Y : SSet.{max u v}}
    (f : (SSet.uliftFunctor.{v, u}).obj X ⟶ Y) (e : X _⦋1⦌) (j : Fin 2) :
    f.app (Opposite.op ⦋1⦌) (ULift.up (X.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ j).op e)) =
      Y.σ 0 (f.app (Opposite.op ⦋0⦌) (ULift.up (X.δ j.rev e))) := by
  rw [constantSimplexPullback_degenerate]
  exact congrArg (fun k : ((SSet.uliftFunctor.{v, u}).obj X) _⦋0⦌ ⟶ Y _⦋1⦌ ↦
    k (ULift.up (X.δ j.rev e))) (f.naturality (SimplexCategory.σ (0 : Fin 1)).op)

/-- 同じ反転した持ち上げの像も元の端点像における退化辺。 -/
lemma liftedOppositeConstantSimplexPullback_image_degenerate
    {X : SSet.{u}} {Y : SSet.{max u v}}
    (f : (SSet.uliftFunctor.{v, u}).obj X.op ⟶ Y) (e : X _⦋1⦌) (j : Fin 2) :
    f.app (Opposite.op ⦋1⦌)
      (ULift.up (SSet.opObjEquiv.symm (X.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ j).op e))) =
      Y.σ 0 (f.app (Opposite.op ⦋0⦌) (ULift.up (SSet.opObjEquiv.symm (X.δ j.rev e)))) := by
  rw [oppositeConstantSimplexPullback_degenerate]
  exact congrArg (fun k : ((SSet.uliftFunctor.{v, u}).obj X.op) _⦋0⦌ ⟶ Y _⦋1⦌ ↦
    k (ULift.up (SSet.opObjEquiv.symm (X.δ j.rev e))))
      (f.naturality (SimplexCategory.σ (0 : Fin 1)).op)

end SerrePositivity.InfinityCategories.F2
