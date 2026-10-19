module

public import SerrePositivity.InfinityCategories.F1B.KanIsofibrationCriterion
public import SerrePositivity.InfinityCategories.Core.EquivalencePathIso

/-!
概要：指定部分・終端・標的の可逆 path を同時に保つ延長。
方針：相対可逆 path 比較の自明 Kan 性を任意の単射へ適用する。
規約：標的の path 自体を固定し、像の同型だけでは置き換えない。
使われ方：相対 Kan 図式を元と標的の図式を変えずに厳密化する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：可逆 path の族は部分図式・終点・標的の像を固定して延長できる。
方針：相対 path の終点比較の単射に対する持ち上げを選ぶ。
規約：単射 i の始域と終域には quasicategory 性を要求しない。
使われ方：部分図式上の指定同値を底の図式を変えずに延長する。 -/
lemma exists_kanRelativeEquivalencePath_extension {A B D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) (hU : KanEquivalenceLifting U)
    (i : A ⟶ B) [Mono i] (a : A ⟶ equivalencePath D)
    (P : B ⟶ equivalencePath E) (f : B ⟶ D)
    (ha : a ≫ equivalencePathMap U = i ≫ P)
    (hf : a ≫ equivalencePathEndpoint D 1 = i ≫ f)
    (hP : P ≫ equivalencePathEndpoint E 1 = f ≫ U) :
    ∃ L : B ⟶ equivalencePath D, i ≫ L = a ∧
      L ≫ equivalencePathMap U = P ∧ L ≫ equivalencePathEndpoint D 1 = f := by
  have : InnerFibration U := hU.innerFibration
  have := kanRelativeEquivalencePathMapAt_one_trivialKanFibration U
    (KanEquivalenceLifting.invertibleTargetLifting hU)
  have := TrivialKanFibration.mem (p := relativeEquivalencePathMapAt U 1) i inferInstance
  let t : B ⟶ relativeEquivalencePathTargetAt U 1 := pullback.lift P f hP
  let sq : CommSq a i (relativeEquivalencePathMapAt U 1) t := by
    constructor
    apply pullback.hom_ext
    · simp only [Category.assoc, relativeEquivalencePathMapAt_fst, t, pullback.lift_fst]
      exact ha
    · simp only [Category.assoc, relativeEquivalencePathMapAt_snd, t, pullback.lift_snd]
      exact hf
  refine ⟨sq.lift, sq.fac_left, ?_, ?_⟩
  · rw [← relativeEquivalencePathMapAt_fst U 1, ← Category.assoc, sq.fac_right]
    exact pullback.lift_fst _ _ _
  · rw [← relativeEquivalencePathMapAt_snd U 1, ← Category.assoc, sq.fac_right]
    exact pullback.lift_snd _ _ _

/-- 概要：可逆 path の族の両端は関手圏内で同型。
方針：可逆 path を uncurry して、全ての垂直辺の可逆性を読む。
規約：パラメータ B は任意の単体集合。
使われ方：厳密化した図式へ標準局所 Kan 条件を移送する。 -/
def kanEquivalencePath_functorIso {B D : SSet.{u}} [Quasicategory D]
    (L : B ⟶ equivalencePath D) :
    FunctorIso (L ≫ equivalencePathEndpoint D 0) (L ≫ equivalencePathEndpoint D 1) := by
  let H := uncurry (L ≫ equivalencePathι D)
  have hC : curry H = L ≫ equivalencePathι D := curry_uncurry _
  have he (j : Fin 2) : prismEndpoint j B ≫ H = L ≫ equivalencePathEndpoint D j := by
    rw [← curry_evaluateFunctorAt_interval, hC]
    rfl
  have e := functorIsoOfEquivalenceHomotopy H (fun x ↦ by
    have hx := fullSubcomplexOnVertices_vertex (L.app (Opposite.op ⦋0⦌) x)
    change IsEquivalencePathVertex ((L ≫ equivalencePathι D).app (Opposite.op ⦋0⦌) x) at hx
    rw [← hC] at hx
    exact hx)
  rw [he 0, he 1] at e
  exact e

end SerrePositivity.InfinityCategories.F1B
