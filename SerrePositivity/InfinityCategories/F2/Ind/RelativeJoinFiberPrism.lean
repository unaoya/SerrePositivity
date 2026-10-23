module

public import SerrePositivity.InfinityCategories.F2.Ind.RelativeJoinFiberEmbedding
public import SerrePositivity.InfinityCategories.Core.FatJoinComparisonNaturality
public import SerrePositivity.InfinityCategories.F1.Joins.RelativeJoinBaseProjection

/-!
概要：元の相対 join の fiber 余錐の全円柱は、元の相対 join prism の同じ fiber 制限。
方針：元の fiber 包含の通常 join 成分と底成分を使い、円柱の自然性で両射影を比較する。
規約：元の fiber 同型・包含・prism を固定。使われ方：同じ全単位の局所余極限性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {K C : SSet.{u}} (p : K ⟶ C) (c : C _⦋0⦌)

/-- 元の fiber 上では、対角円柱の右係数は指定頂点に定値になる。 -/
lemma relativeJoinFiberPrism_parameter :
    fst ((vertexFiber p c) ⊗ (Δ[1] : SSet.{u})) Δ[0] ≫
      (vertexFiberι p c ▷ (Δ[1] : SSet.{u})) ≫ (β_ K (Δ[1] : SSet.{u})).hom ≫
        joinDiagonalCylinder K ≫ fatJoinCylinderMap (𝟙 K) p =
      fatJoinCylinderMap (vertexFiberι p c) (SSet.const c : (Δ[0] : SSet.{u}) ⟶ C) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro z
  apply Prod.ext
  · rfl
  · exact z.1.1.property

/-- 同じ元の fiber 余錐の全円柱は、元の全相対 join prism の同じ fiber 制限そのもの。 -/
lemma relativeJoinFiberEmbedding_prism :
    joinCylinderMap (vertexFiber p c) Δ[0] ≫ relativeJoinFiberEmbedding p c =
      fst ((vertexFiber p c) ⊗ (Δ[1] : SSet.{u})) Δ[0] ≫
        (vertexFiberι p c ▷ (Δ[1] : SSet.{u})) ≫ (β_ K (Δ[1] : SSet.{u})).hom ≫
          relativeJoinPrism p := by
  have hf : (joinCylinderMap (vertexFiber p c) Δ[0] ≫ relativeJoinFiberEmbedding p c) ≫
      pullback.fst (joinMap p (𝟙 C)) (joinDiagonal C) =
      (fst ((vertexFiber p c) ⊗ (Δ[1] : SSet.{u})) Δ[0] ≫
        (vertexFiberι p c ▷ (Δ[1] : SSet.{u})) ≫ (β_ K (Δ[1] : SSet.{u})).hom ≫
          relativeJoinPrism p) ≫ pullback.fst (joinMap p (𝟙 C)) (joinDiagonal C) := by
    rw [Category.assoc, relativeJoinFiberEmbedding_fst p c]
    simp only [Category.assoc, relativeJoinPrism,
      pullback.lift_fst, joinDiagonal, ← joinCylinderMap_naturality]
    simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ joinCylinderMap K C)
      (relativeJoinFiberPrism_parameter p c).symm
  apply pullback.hom_ext
  · exact hf
  · apply CartesianMonoidalCategory.hom_ext
    · change (joinCylinderMap (vertexFiber p c) Δ[0] ≫ relativeJoinFiberEmbedding p c) ≫
        relativeJoinProjection p (𝟙 C) = _ ≫ relativeJoinProjection p (𝟙 C)
      rw [relativeJoinProjection_eq_fst_interval]
      simpa only [Category.assoc] using
        congrArg (fun f ↦ f ≫ joinIntervalProjection K C) hf
    · change joinCylinderMap (vertexFiber p c) Δ[0] ≫ relativeJoinFiberEmbedding p c ≫
        relativeJoinBaseProjection p (𝟙 C) =
        fst ((vertexFiber p c) ⊗ (Δ[1] : SSet.{u})) Δ[0] ≫
          (vertexFiberι p c ▷ (Δ[1] : SSet.{u})) ≫ (β_ K (Δ[1] : SSet.{u})).hom ≫
            relativeJoinPrism p ≫ relativeJoinBaseProjection p (𝟙 C)
      rw [relativeJoinFiberEmbedding_base, relativeJoinPrism_baseProjection]
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro z
      exact z.1.1.property.symm

end SerrePositivity.InfinityCategories.F2.Ind
