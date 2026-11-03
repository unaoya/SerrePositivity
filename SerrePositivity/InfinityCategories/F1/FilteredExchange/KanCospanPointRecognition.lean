module

public import SerrePositivity.InfinityCategories.Core.EquivalencePath
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.PrismContraction
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalPullbackCoordinates
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.KanCospanPathEndpoints
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.KanCospanPoint

/-!
概要：元の二入力を持つ Kan 引き戻し射を、元の指定全 path の表示へ戻す。
方針：元の path 座標を uncurry し、端点を二入力の式で照合する。
規約：表示は元の射と厳密に一致し、path を選び直さない。
使われ方：任意の有限標的射を元の二入力の場合の検出へ接続する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：二入力が元の入力の単位像なら、元の Kan 引き戻し射を指定 path 表示できる。
方針：指定 path をそのまま uncurry し、三座標の一致を確認する。
規約：等式による表示。使われ方：任意の標的射の有限検出。 -/
lemma kanCospanPoint_recognition {K E D H : SSet.{u}} (f : E ⟶ H) (g : D ⟶ H)
    (a : K ⟶ intervalPullback (continuousKanReplacement.map f) (continuousKanReplacement.map g))
    (u : K ⟶ E) (v : K ⟶ D)
    (hl : a ≫ intervalPullbackLeft (continuousKanReplacement.map f)
      (continuousKanReplacement.map g) = u ≫ continuousKanReplacementUnit.app E)
    (hr : a ≫ intervalPullbackRight (continuousKanReplacement.map f)
      (continuousKanReplacement.map g) = v ≫ continuousKanReplacementUnit.app D) :
    ∃ L : SSet.Homotopy (u ≫ f ≫ continuousKanReplacementUnit.app H)
      (v ≫ g ≫ continuousKanReplacementUnit.app H), a = kanCospanPoint f g u v L := by
  let q := a ≫ intervalPullbackPath (continuousKanReplacement.map f)
    (continuousKanReplacement.map g)
  let L : SSet.Homotopy
      ((u ≫ continuousKanReplacementUnit.app E) ≫ continuousKanReplacement.map f)
      ((v ≫ continuousKanReplacementUnit.app D) ≫ continuousKanReplacement.map g) :=
    { h := (β_ K (Δ[1] : SSet.{u})).hom ≫ uncurry q
      h₀ := by
        change prismEndpoint 0 K ≫ uncurry q =
          (u ≫ continuousKanReplacementUnit.app E) ≫ continuousKanReplacement.map f
        rw [← curry_evaluateFunctorAt_interval, curry_uncurry]
        change (a ≫ intervalPullbackPath _ _) ≫ (intervalEndpointNatTrans 0).app _ = _
        rw [Category.assoc, intervalPullbackPath_zero, ← Category.assoc, hl]
      h₁ := by
        change prismEndpoint 1 K ≫ uncurry q =
          (v ≫ continuousKanReplacementUnit.app D) ≫ continuousKanReplacement.map g
        rw [← curry_evaluateFunctorAt_interval, curry_uncurry]
        change (a ≫ intervalPullbackPath _ _) ≫ (intervalEndpointNatTrans 1).app _ = _
        rw [Category.assoc, intervalPullbackPath_one, ← Category.assoc, hr]
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro x
        exact False.elim x.1.property }
  refine ⟨kanCospanRawPath f g u v L, ?_⟩
  apply intervalPullback_hom_ext
  · rw [kanCospanPoint_path]
    change q = curry ((β_ (Δ[1] : SSet.{u}) K).hom ≫
      (β_ K (Δ[1] : SSet.{u})).hom ≫ uncurry q)
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp, curry_uncurry]
  · rw [kanCospanPoint_left, hl]
  · rw [kanCospanPoint_right, hr]

end SerrePositivity.InfinityCategories.F2
