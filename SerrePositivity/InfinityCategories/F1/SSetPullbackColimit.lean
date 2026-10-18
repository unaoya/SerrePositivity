module

public import SerrePositivity.InfinityCategories.F1.TypesPullbackColimit
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
概要：単体集合の余極限の cocone を pullback した cocone の余極限性。
方針：評価関手で各次数の型へ移し、型の pullback の余極限保存を適用する。
規約：通常の単体集合の圏の余極限だけを扱う。
使われ方：Kerodon Proposition 5.2.4.5、relative join の左因子の余極限保存。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory Limits
namespace SerrePositivity.InfinityCategories

/-- 概要：単体集合の余極限の脚を pullback した cocone は余極限。
方針：各次数の型の余極限を pullback し、評価関手による余極限の反映を使う。
規約：添字は宇宙 u で小さく、射の単射性は要求しない。
使われ方：Kerodon Proposition 5.2.4.5、セルの族と骨格列の比較の貼り合わせ。 -/
noncomputable def sset_isColimit_of_pullback {J : Type v} [Category.{w} J] [Small.{u} J]
    {D E : J ⥤ SSet.{u}} (c : Cocone D) (hc : IsColimit c) (d : Cocone E)
    (α : E ⟶ D) (f : d.pt ⟶ c.pt)
    (hp : ∀ j, IsPullback (d.ι.app j) (α.app j) f (c.ι.app j)) : IsColimit d := by
  apply evaluationJointlyReflectsColimits
  intro n
  let ev := (evaluation SimplexCategoryᵒᵖ (Type u)).obj n
  exact types_isColimit_of_pullback (ev.mapCocone c) (isColimitOfPreserves ev hc)
    (ev.mapCocone d) (Functor.whiskerRight α ev) (f.app n) (fun j ↦ (hp j).app n)

end SerrePositivity.InfinityCategories
