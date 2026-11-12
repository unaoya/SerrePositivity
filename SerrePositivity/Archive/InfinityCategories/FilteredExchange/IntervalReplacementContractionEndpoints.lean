module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.IntervalReplacementContraction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConstantDiagram

/-!
概要：区間置換内の指定収縮の両端を元の定値切断と恒等射に同定する。
方針：path 座標は形状収縮の両端、入力座標は同じ射として比較する。
規約：元の切断を使用。使われ方：全 path を保つ指定関手同型の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {X Y : SSet.{u}} [KanComplex Y] (f : X ⟶ Y)
local notation "P" => intervalReplacement f
local notation "pa" => pullback.fst (NatTrans.app (intervalEndpointNatTrans 0) Y) f
local notation "pr" => pullback.snd (NatTrans.app (intervalEndpointNatTrans 0) Y) f

/-- 時刻零では元の入力における元の定値切断そのものになる。 -/
lemma intervalReplacementContraction_zero :
    SSet.ι₀ ≫ intervalReplacementContraction f = pr ≫ intervalReplacementSection f := by
  apply pullback.hom_ext (f := (intervalEndpointNatTrans 0).app Y) (g := f)
  · simp only [Category.assoc, intervalReplacementContraction_path,
      intervalReplacementSection_path]
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, ← Category.assoc,
      intervalShapeContraction_zero, Category.assoc,
      ← curry_evaluateFunctorAt_interval, curry_uncurry]
    change _ = uncurry ((pr ≫ f) ≫ constantDiagram Δ[1] Y)
    rw [uncurry_comp_constantDiagram]
    have h : pa ≫ (intervalEndpointNatTrans 0).app Y = pr ≫ f := pullback.condition
    exact congrArg (fun k : P ⟶ Y => snd Δ[1] P ≫ k) h
  · rw [Category.assoc, intervalReplacementContraction_input, Category.assoc,
      intervalReplacementSection_projection, Category.comp_id]
    rfl

/-- 時刻一では元の path を含む置換の恒等射そのものになる。 -/
lemma intervalReplacementContraction_one :
    SSet.ι₁ ≫ intervalReplacementContraction f = 𝟙 P := by
  apply pullback.hom_ext (f := (intervalEndpointNatTrans 0).app Y) (g := f)
  · rw [Category.assoc, intervalReplacementContraction_path, Category.id_comp]
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, ← Category.assoc,
      intervalShapeContraction_one, Category.id_comp]
  · rw [Category.assoc, intervalReplacementContraction_input]
    rfl

end SerrePositivity.InfinityCategories.F2
