module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalReplacementPath

/-!
概要：元の入力と全ホモトピーから区間 path 置換への射を構成する。
方針：全円柱の curry と入力を引き戻しへ入れ、三つの制限を照合する。
規約：指定された全 path を保持。使われ方：終点射の境界充填の実際の射。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {K X Y : SSet.{u}} (f : X ⟶ Y) (a : K ⟶ X) (b : K ⟶ Y)
  (H : SSet.Homotopy (a ≫ f) b)

/-- 概要：元の入力と指定全円柱を path 置換へ入れる。
方針：curry と入力の引き戻し。規約：全 path を保持。使われ方：終点射の持ち上げ。 -/
def intervalReplacementHomotopyPoint : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacement f :=
  pullback.lift (curry ((β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h)) a (by
    change curry _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) = a ≫ f
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval]
    exact H.h₀)

/-- 概要：指定全 path の回収。
方針：第一射影。規約：厳密な式。使われ方：境界 path の照合。 -/
lemma intervalReplacementHomotopyPoint_path :
    intervalReplacementHomotopyPoint f a b H ≫
      pullback.fst ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app Y) f =
        curry ((β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h) := pullback.lift_fst _ _ _

/-- 概要：元の入力の回収。
方針：第二射影。規約：厳密な式。使われ方：持ち上げの元の境界入力。 -/
lemma intervalReplacementHomotopyPoint_input :
    intervalReplacementHomotopyPoint f a b H ≫
      pullback.snd ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app Y) f = a := pullback.lift_snd _ _ _

/-- 概要：終点射との合成は指定標的射。
方針：全 path の終点評価。規約：厳密な式。使われ方：持ち上げの標的条件。 -/
lemma intervalReplacementHomotopyPoint_endpoint :
    intervalReplacementHomotopyPoint f a b H ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint f = b := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint, ← Category.assoc, intervalReplacementHomotopyPoint_path]
  change curry _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) = b
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval]
  exact H.h₁

/-- 概要：入力と全境界円柱を保てば、元の境界の path 置換射にも厳密に制限する。
方針：両射影と curry の自然性。規約：全単体。使われ方：境界充填の始域条件。 -/
lemma intervalReplacementHomotopyPoint_restrict {A : SSet.{u}} (i : A ⟶ K)
    (u : A ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacement f)
    (ha : i ≫ a = u ≫ pullback.snd ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app Y) f)
    (hH : (i ▷ (Δ[1] : SSet.{u})) ≫ H.h = (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementPathHomotopy f u).h) :
    i ≫ intervalReplacementHomotopyPoint f a b H = u := by
  apply pullback.hom_ext
  · rw [Category.assoc, intervalReplacementHomotopyPoint_path, ← curry_natural_left]
    change curry ((β_ (Δ[1] : SSet.{u}) A).hom ≫
      ((i ▷ (Δ[1] : SSet.{u})) ≫ H.h)) = _
    rw [hH, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementPathHomotopy_curry]
  · rw [Category.assoc, intervalReplacementHomotopyPoint_input, ha]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
