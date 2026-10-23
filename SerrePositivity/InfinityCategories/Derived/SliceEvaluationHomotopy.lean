module
public import SerrePositivity.InfinityCategories.Derived.FunctorSliceTerminal
public import SerrePositivity.InfinityCategories.Derived.HomotopyPostcomposition
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorFiber
public import SerrePositivity.InfinityCategories.F1.Joins.SlicePrismSquare

/-!
概要：実 slice の普遍錐を全パラメータの実評価ホモトピーとして表示する。
方針：右 join prism を展開し、同じ後合成ホモトピーを関手圏へ移す。
規約：恒等錐上の全時刻を厳密に固定する。使われ方：共有実評価の成分の照合。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
/-- 実 slice の普遍錐を、その始域射影から定値終点への同じ実ホモトピーにする。 -/
def roofSliceEvaluationHomotopy {X : SSet.{u}} (z : X _⦋0⦌) :
    SSet.Homotopy (sliceOverProjection (SSet.yonedaEquiv.symm z)) (SSet.const z) where
  h := (β_ (sliceOver (SSet.yonedaEquiv.symm z)) (Δ[1] : SSet.{u})).hom ≫
    rightMappingSpacePrism _ ≫ sliceOverUncurry (𝟙 _)
  h₀ := by
    change prismEndpoint 0 (sliceOver (SSet.yonedaEquiv.symm z)) ≫
      rightMappingSpacePrism (sliceOver (SSet.yonedaEquiv.symm z)) ≫
        sliceOverUncurry (𝟙 (sliceOver (SSet.yonedaEquiv.symm z))) =
          sliceOverProjection (SSet.yonedaEquiv.symm z)
    rw [← Category.assoc, rightMappingSpacePrism_zero, sliceOverUncurry_projection,
      Category.id_comp]
  h₁ := by
    change prismEndpoint 1 (sliceOver (SSet.yonedaEquiv.symm z)) ≫
      rightMappingSpacePrism (sliceOver (SSet.yonedaEquiv.symm z)) ≫
        sliceOverUncurry (𝟙 (sliceOver (SSet.yonedaEquiv.symm z))) =
          (SSet.const z : sliceOver (SSet.yonedaEquiv.symm z) ⟶ X)
    rw [← Category.assoc, rightMappingSpacePrism_one, Category.assoc,
      sliceOverUncurry_fixed, const_point_comp_yoneda]
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property
/-- 恒等錐上では、普遍評価は全時刻で同じ頂点に厳密に定値。 -/
lemma roofSliceEvaluationHomotopy_identity {X : SSet.{u}} (z : X _⦋0⦌) :
    (SSet.yonedaEquiv.symm (sliceIdentityCone z) ▷ (Δ[1] : SSet.{u})) ≫
      (roofSliceEvaluationHomotopy z).h =
        snd (Δ[0] : SSet.{u}) Δ[1] ≫ SSet.const z := by
  dsimp only [roofSliceEvaluationHomotopy]
  have hb : (SSet.yonedaEquiv.symm (sliceIdentityCone z) ▷ (Δ[1] : SSet.{u})) ≫
      (β_ (sliceOver (SSet.yonedaEquiv.symm z)) (Δ[1] : SSet.{u})).hom =
        (β_ (Δ[0] : SSet.{u}) Δ[1]).hom ≫
          (Δ[1] ◁ SSet.yonedaEquiv.symm (sliceIdentityCone z)) := rfl
  rw [← Category.assoc, hb, Category.assoc, ← Category.assoc (Δ[1] ◁ _),
    rightMappingSpacePrism_naturality, Category.assoc, ← sliceOverUncurry_precomp,
    Category.comp_id, sliceOverUncurry_yoneda]
  change _ ≫ SSet.const z = _
  rw [SSet.comp_const, SSet.comp_const]
/-- 全パラメータ関手圏の始域射影から定値終点への普遍評価ホモトピー。 -/
def roofFunctorSliceEvaluationHomotopy (K : SSet.{u}) {X : SSet.{u}} (z : X _⦋0⦌) :
    SSet.Homotopy (roofFunctorSliceProjection K z)
      (SSet.const (functorVertex (SSet.const (X := K) z))) where
  h := (homotopyPostcomposition K (roofSliceEvaluationHomotopy z)).h
  h₀ := (homotopyPostcomposition K (roofSliceEvaluationHomotopy z)).h₀
  h₁ := (homotopyPostcomposition K (roofSliceEvaluationHomotopy z)).h₁.trans (ihom_map_const z)
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property
end SerrePositivity.InfinityCategories
