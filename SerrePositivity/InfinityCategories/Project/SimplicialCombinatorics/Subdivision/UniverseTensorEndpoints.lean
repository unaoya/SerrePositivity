module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.UniverseLiftTensor
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-!
概要：既存の全円柱の宇宙移送は、元の二つの端点の全射を保存する。
方針：元の simplexTensorMap の両端を各次数で評価する。
使われ方：Kerodon §7.3（Tag 02Y1）、HTT 6.2.2.6 の指定右 Kan 輸送の宇宙変更。
規約：円柱の移送自体は作り直さない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-- 元の全円柱の始端の射は、同じ移送の始端に厳密に一致。 -/
lemma simplexTensorMap_zero {A B : SSet.{u}} (h : A ⊗ (Δ[1] : SSet.{u}) ⟶ B) :
    SSet.ι₀ ≫ simplexTensorMap.{v} h = (SSet.uliftFunctor.{v, u}).map (SSet.ι₀ ≫ h) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 元の全円柱の終端の射も、同じ移送の終端に厳密に一致。 -/
lemma simplexTensorMap_one {A B : SSet.{u}} (h : A ⊗ (Δ[1] : SSet.{u}) ⟶ B) :
    SSet.ι₁ ≫ simplexTensorMap.{v} h = (SSet.uliftFunctor.{v, u}).map (SSet.ι₁ ≫ h) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
