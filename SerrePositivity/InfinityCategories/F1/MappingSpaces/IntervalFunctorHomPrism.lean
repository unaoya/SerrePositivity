module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorParameterizedPrism
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingPostIso
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalFatDiagram

/-!
概要：関手圏の実際の区間 Hom の族を、底と区間の積上の prism へ展開する。
方針：二重の uncurry と因子の交換を使い、元の端点と成分評価を計算する。
規約：全パラメーターと元の関手の値を保持する。
使われ方：一次元の固定成分 fiber の三辺固定の正方形表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 関手圏の元の区間 Hom の全パラメーターを、底との積上で評価する。 -/
def intervalFunctorHomPrism {T B X : SSet.{u}} {F G : B ⟶ X}
    (f : T ⟶ intervalMappingSpace (functorVertex F) (functorVertex G)) :
    ((Δ[1] : SSet.{u}) ⊗ B) ⊗ T ⟶ X :=
  functorParameterizedPrism (intervalMappingUncurry f)

/-- 同じ prism の始点は、元の始域図式に全パラメーターで定値。 -/
lemma intervalFunctorHomPrism_zero {T B X : SSet.{u}} {F G : B ⟶ X}
    (f : T ⟶ intervalMappingSpace (functorVertex F) (functorVertex G)) :
    (prismEndpoint 0 B ▷ T) ≫ intervalFunctorHomPrism f = fst B T ≫ F := by
  apply functorParameterizedPrism_vertex_of_const 1 (intervalMappingUncurry f) 0 F
  exact intervalMappingUncurry_zero f

/-- 同じ prism の終点は、元の標的図式に全パラメーターで定値。 -/
lemma intervalFunctorHomPrism_one {T B X : SSet.{u}} {F G : B ⟶ X}
    (f : T ⟶ intervalMappingSpace (functorVertex F) (functorVertex G)) :
    (prismEndpoint 1 B ▷ T) ≫ intervalFunctorHomPrism f = fst B T ≫ G := by
  apply functorParameterizedPrism_vertex_of_const 1 (intervalMappingUncurry f) 1 G
  exact intervalMappingUncurry_one f

/-- 同じ prism の底の頂点への制限は、元の Hom の成分評価を展開したもの。 -/
lemma intervalFunctorHomPrism_evaluate {T B X : SSet.{u}} {F G : B ⟶ X}
    (f : T ⟶ intervalMappingSpace (functorVertex F) (functorVertex G)) (b : B _⦋0⦌) :
    (lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const b) ▷ T) ≫ intervalFunctorHomPrism f =
      intervalMappingUncurry (f ≫ intervalMappingPostOfEq (evaluateFunctorAt b)
        (functorVertex F) (functorVertex G) (evaluateFunctorAt_functorVertex b F)
          (evaluateFunctorAt_functorVertex b G)) := by
  rw [intervalMappingPostOfEq_uncurry]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨i, t⟩
  rfl

/-- 指定した端点への正規化を含む成分評価も、同じ prism の頂点制限そのもの。 -/
lemma intervalFunctorHomPrism_evaluateOfEq {T B X : SSet.{u}} {F G : B ⟶ X}
    (f : T ⟶ intervalMappingSpace (functorVertex F) (functorVertex G)) (b : B _⦋0⦌)
    {x y : X _⦋0⦌}
    (hx : (evaluateFunctorAt (Y := X) b).app _ (functorVertex F) = x)
    (hy : (evaluateFunctorAt (Y := X) b).app _ (functorVertex G) = y) :
    (lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const b) ▷ T) ≫ intervalFunctorHomPrism f =
      intervalMappingUncurry (f ≫ intervalMappingPostOfEq (evaluateFunctorAt b)
        (functorVertex F) (functorVertex G) hx hy) := by
  rw [intervalMappingPostOfEq_uncurry]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨i, t⟩
  rfl

/-- 元の関手圏の区間 Hom の族は、この prism 全体で一意に決まる。 -/
lemma intervalFunctorHomPrism_injective {T B X : SSet.{u}} (F G : B ⟶ X) :
    Function.Injective (intervalFunctorHomPrism (T := T) (F := F) (G := G)) := by
  intro f g h
  unfold intervalFunctorHomPrism functorParameterizedPrism at h
  have h₁ := (cancel_epi ((β_ (Δ[1] : SSet.{u}) B).hom ▷ T)).mp h
  have h₂ := (cancel_epi (α_ B (Δ[1] : SSet.{u}) T).hom).mp h₁
  exact intervalMappingUncurry_injective _ _ (uncurry_injective h₂)

end SerrePositivity.InfinityCategories
