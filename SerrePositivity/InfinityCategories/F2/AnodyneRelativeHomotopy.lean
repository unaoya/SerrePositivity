module

public import SerrePositivity.InfinityCategories.F2.FiberwiseIntervalKanComparison
public import SerrePositivity.InfinityCategories.F2.ArrowBoundaryNaturality
public import SerrePositivity.InfinityCategories.Core.HomotopyBoundaryExtension

/-!
概要：anodyne な部分図式上で一致する二射を、その部分上で定値な円柱で比較する。
方針：両端評価への持ち上げで全 path を選び、指定した定値部分 path を厳密に保つ。
規約：ホモトピー類だけでなく制限された全円柱を保持する。
使われ方：Kan 置換から元の値へ戻す path の端点固定比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open HomotopicalAlgebra SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：anodyne な部分上で一致する二射は、その部分を固定してホモトピック。
方針：Kan な両端評価へ定値 path の延長を持ち上げる。
規約：部分円柱は全時刻で厳密に定値。使われ方：単位の強変形 retract。 -/
lemma anodyne_relative_homotopy {A K X : SSet.{u}} [KanComplex X]
    (i : A ⟶ K) (hi : anodyneExtensions i) (f g : K ⟶ X) (h : i ≫ f = i ≫ g) :
    ∃ H : SSet.Homotopy f g,
      (i ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A (Δ[1] : SSet.{u}) ≫ i ≫ f := by
  have := hi (arrowEndpointPair X)
    (by rw [← HomotopicalAlgebra.fibration_iff]; infer_instance)
  let a := (i ≫ f) ≫ constantDiagram (Δ[1] : SSet.{u}) X
  have sq : CommSq a i (arrowEndpointPair X) (lift f g) := ⟨by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [a, arrowEndpointPair, Category.assoc, lift_fst,
        constantDiagram_evaluate, Category.comp_id]
    · simp only [a, arrowEndpointPair, Category.assoc, lift_snd,
        constantDiagram_evaluate, Category.comp_id]
      exact h⟩
  let R := (β_ K (Δ[1] : SSet.{u})).hom ≫ uncurry sq.lift
  have hzero : SSet.ι₀ ≫ R = f := by
    change prismEndpoint 0 K ≫ uncurry sq.lift = f
    rw [← curry_evaluateFunctorAt_interval, curry_uncurry]
    exact congrArg (fun r ↦ r ≫ fst X X) sq.fac_right
  have hone : SSet.ι₁ ≫ R = g := by
    change prismEndpoint 1 K ≫ uncurry sq.lift = g
    rw [← curry_evaluateFunctorAt_interval, curry_uncurry]
    exact congrArg (fun r ↦ r ≫ snd X X) sq.fac_right
  refine ⟨⟨R, hzero, hone, ?_⟩, ?_⟩
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property
  · change (i ▷ (Δ[1] : SSet.{u})) ≫ R = _
    dsimp only [R]
    rw [← Category.assoc, BraidedCategory.braiding_naturality_left, Category.assoc,
      ← uncurry_natural_left, sq.fac_left]
    dsimp only [a]
    rw [uncurry_comp_constantDiagram]
    rfl

end SerrePositivity.InfinityCategories.F2
