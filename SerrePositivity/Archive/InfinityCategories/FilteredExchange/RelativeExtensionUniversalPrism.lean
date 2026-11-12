module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionUniversalInitial
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PrismLiftSpace
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.TransformationFamilyDiagram

/-!
概要：同じ底と初期値を保つ全 prism の普遍評価を、元の全係数上の実 prism にする。
方針：全延長の uncurry を結合子で表示し、初期値と底を回収する。
規約：全選択空間と全初期値を保持。使われ方：最初辺の全持ち上げに沿う三角形の族。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {K E B : SSet.{u}} (p : E ⟶ B) (β : (Δ[1] : SSet.{u}) ⊗ K ⟶ B)
  (v : K ⟶ E) (hv : v ≫ p = prismEndpoint 0 K ≫ β)
local notation "Q" => relativeFunctorExtensionSpace p β (prismEndpoint 0 K) v hv
local notation "R" => relativeFunctorUncurry
  (relativeFunctorExtensionSpaceι p β (prismEndpoint 0 K) v hv)

/-- 元の全 prism 選択空間上の、同じ元の実全評価 prism。 -/
def relativeExtensionUniversalPrism : (Δ[1] : SSet.{u}) ⊗ (K ⊗ Q) ⟶ E :=
  (α_ Δ[1] K Q).inv ≫ R

/-- 元の全選択で同じ初期値を保つ、全実 prism の始点式。 -/
lemma relativeExtensionUniversalPrism_start :
    prismEndpoint 0 (K ⊗ Q) ≫ relativeExtensionUniversalPrism p β v hv = fst K Q ≫ v := by
  rw [relativeExtensionUniversalPrism, ← Category.assoc, prismEndpoint_associator_inv,
    relativeExtensionUniversal_initial]

/-- 元の全実 prism の底は、元の同じ辺の底を全選択で引き戻したもの。 -/
lemma relativeExtensionUniversalPrism_projection :
    relativeExtensionUniversalPrism p β v hv ≫ p = (Δ[1] ◁ fst K Q) ≫ β := by
  rw [relativeExtensionUniversalPrism, Category.assoc, relativeFunctorUncurry_projection]
  have hn : (α_ Δ[1] K Q).inv ≫ fst ((Δ[1] : SSet.{u}) ⊗ K) Q = Δ[1] ◁ fst K Q := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro k
    rfl
  simpa only [Category.assoc] using congrArg (fun q => q ≫ β) hn

end SerrePositivity.InfinityCategories.F2
