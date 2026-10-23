module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningMappingVertexRecovery

/-!
概要：c1 の指定変換頂点の実際の作用に、全パラメータ上の pointed 持ち上げを付ける。
方針：普遍的な持ち上げを指定変換頂点と指定全空間射で制限する。
規約：始値・終値とも元の選択済みの比較射そのもの。
使われ方：同じ恒等点復元射上の評価を、指定区間族の普遍輸送と比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {B M : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u})
  (t : (leftUnstraighteningTransformationSpace F G) _⦋0⦌) (r : M ⟶ leftUnstraightening F)

/-- c1 の元の全持ち上げを、指定変換と元の全パラメータへ制限する。 -/
def mappingVertexLiftPrism : (Δ[1] : SSet.{u + 1}) ⊗ M ⟶ PointedSpaceInfinity.{u} :=
  lift (Δ[1] ◁ r) (SSet.const t) ≫ leftUnstraighteningTransformationFamilyLift F G

lemma mappingVertexLiftPrism_endpoint (i : Fin 2) :
    prismEndpoint i M ≫ mappingVertexLiftPrism F G t r =
      r ≫ lift (𝟙 (leftUnstraightening F)) (SSet.const t) ≫
        (simplexPrismVertex 1 i (leftUnstraightening F) ▷
          leftUnstraighteningTransformationSpace F G) ≫
        leftUnstraighteningTransformationFamilyLift F G := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- 制限した全持ち上げの始値は、元の全空間射の pointed 成分そのもの。 -/
lemma mappingVertexLiftPrism_start :
    prismEndpoint 0 M ≫ mappingVertexLiftPrism F G t r =
      r ≫ pullback.fst pointedSpaceProjection F := by
  rw [mappingVertexLiftPrism_endpoint, leftUnstraighteningTransformationFamilyLift_start]
  simp only [← Category.assoc, lift_fst, Category.comp_id]

/-- 同じ全持ち上げの終値は、c1 の指定頂点の元の射の pointed 成分そのもの。 -/
lemma mappingVertexLiftPrism_finish :
    prismEndpoint 1 M ≫ mappingVertexLiftPrism F G t r =
      r ≫ (leftUnstraighteningMappingVertexMap F G t).val ≫
        pullback.fst pointedSpaceProjection G := by
  rw [mappingVertexLiftPrism_endpoint, leftUnstraighteningMappingVertexMap_eq_family]
  simp only [Category.assoc, leftUnstraighteningMappingFamily, pullback.lift_fst]

/-- 同じ全持ち上げの底は、元の指定変換の全円柱を元の射影で引き戻したもの。 -/
lemma mappingVertexLiftPrism_projection :
    mappingVertexLiftPrism F G t r ≫ pointedSpaceProjection =
      (Δ[1] ◁ (r ≫ leftUnstraighteningProjection F)) ≫
        functorEdgePrism (intervalMappingEdgeOfVertex t) := by
  have ht : intervalMappingVertexOfEdge (intervalMappingEdgeOfVertex t) = t :=
    (intervalMappingEdgeVertexEquiv _ _).apply_symm_apply t
  have hh : mappingVertexLiftPrism F G t r ≫ pointedSpaceProjection =
      (Δ[1] ◁ (r ≫ leftUnstraighteningProjection F)) ≫
        lift (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ B)) (SSet.const t) ≫
          leftUnstraighteningTransformationFamily F G := by
    rw [mappingVertexLiftPrism, Category.assoc,
      leftUnstraighteningTransformationFamilyLift_projection]
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  rw [hh]
  exact congrArg (fun f => (Δ[1] ◁ (r ≫ leftUnstraighteningProjection F)) ≫ f)
    (by simpa only [ht] using
      leftUnstraighteningTransformationFamily_at_edge F G (intervalMappingEdgeOfVertex t))

end SerrePositivity.InfinityCategories.F2.Ind
