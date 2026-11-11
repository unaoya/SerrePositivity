module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.IntervalShapeEndpoints
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalReplacementPathSection

/-!
概要：区間置換の各 path を始点の定値 path から元の path へ変形する。
方針：形状収縮を curry し、元の入力を全時刻で固定して引き戻しへ戻す。
規約：元の全 path を保持。使われ方：二つの引き戻し比較の指定関手同型。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {X Y : SSet.{u}} (f : X ⟶ Y)
local notation "P" => intervalReplacement f
local notation "pa" => pullback.fst (NatTrans.app (intervalEndpointNatTrans 0) Y) f
local notation "pr" => pullback.snd (NatTrans.app (intervalEndpointNatTrans 0) Y) f

/-- 入力を固定し、元の全 path の形状を時刻とともに伸ばす置換内の射。 -/
def intervalReplacementContraction : P ⊗ (Δ[1] : SSet.{u}) ⟶ P :=
  pullback.lift (curry (intervalShapeContraction P ≫ uncurry pa)) (fst P Δ[1] ≫ pr) (by
    change curry (intervalShapeContraction P ≫ uncurry pa) ≫ evaluateFunctorAt _ = _
    rw [curry_evaluateFunctorAt_interval, ← Category.assoc,
      intervalShapeContraction_path_zero, Category.assoc,
      ← curry_evaluateFunctorAt_interval, curry_uncurry]
    have h : pa ≫ (intervalEndpointNatTrans 0).app Y = pr ≫ f := pullback.condition
    exact (congrArg (fun k : P ⟶ Y => fst P Δ[1] ≫ k) h).trans
      (Category.assoc _ _ _).symm)

/-- 変形の全 path 座標は元の指定した形状収縮そのもの。 -/
lemma intervalReplacementContraction_path :
    intervalReplacementContraction f ≫ pa = curry (intervalShapeContraction P ≫ uncurry pa) :=
  pullback.lift_fst _ _ _

/-- 変形は元の入力を全時刻で固定する。 -/
lemma intervalReplacementContraction_input :
    intervalReplacementContraction f ≫ pr = fst P Δ[1] ≫ pr := pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.F2
