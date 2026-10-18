module

public import SerrePositivity.InfinityCategories.Core.FixedDiagramCylinderIso
public import SerrePositivity.InfinityCategories.Core.JoinEquivalenceFunctor
public import SerrePositivity.InfinityCategories.Core.JoinTensor

/-!
概要：join の可逆円柱上の族の両端は固定図式上で同型。
方針：左因子の円柱の射影の普遍的同値性を join で保ち、二つの端点制限を比較する。
規約：右因子の図式を固定する。
使われ方：Kerodon Lemma 4.6.4.25 の slice の同型の保存。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：可逆区間との直積からの第一射影は普遍的な前合成の同値条件を満たす。
方針：端点包含との合成が恒等であることから二対三則を使う。
規約：A は任意。
使われ方：Kerodon §4.6.4 の圏論的円柱の射影。 -/
lemma isPrecompositionEquivalence_equivalenceCylinder_fst (A : SSet.{u}) :
    IsPrecompositionEquivalence (fst A equivalenceInterval) := by
  apply (isPrecompositionEquivalence_equivalenceCylinderEndpoint A false).cancel_left
  rw [equivalenceCylinderEndpoint_fst]
  exact isPrecompositionEquivalence_id _

/-- 概要：可逆円柱との join の射影は普遍的な前合成の同値条件を満たす。
方針：左因子の join が普遍的同値を保つことを使う。
規約：二つの因子は任意。
使われ方：Kerodon Lemma 4.6.4.25 の join の圏論的円柱。 -/
lemma isPrecompositionEquivalence_joinCylinderProjection (A K : SSet.{u}) :
    IsPrecompositionEquivalence (joinMap (fst A equivalenceInterval) (𝟙 K)) :=
  (isPrecompositionEquivalence_equivalenceCylinder_fst A).joinMap_left K

/-- 概要：join の可逆円柱の射影はエピ射。
方針：false 端による厳密な切断を使う。
規約：両因子の非空性は不要。
使われ方：Kerodon §4.6.4 の前合成の単射性。 -/
instance joinCylinderProjection_epi (A K : SSet.{u}) :
    Epi (joinMap (fst A equivalenceInterval) (𝟙 K)) := by
  let a := joinMap (equivalenceCylinderEndpoint A false) (𝟙 K)
  have ha : a ≫ joinMap (fst A equivalenceInterval) (𝟙 K) = 𝟙 _ := by
    dsimp [a]
    rw [← joinMap_comp, equivalenceCylinderEndpoint_fst, Category.id_comp, joinMap_id]
  constructor
  intro Y f g h
  calc
    f = (a ≫ joinMap (fst A equivalenceInterval) (𝟙 K)) ≫ f := by rw [ha, Category.id_comp]
    _ = a ≫ (joinMap (fst A equivalenceInterval) (𝟙 K) ≫ g) := by rw [Category.assoc, h]
    _ = g := by rw [← Category.assoc, ha, Category.id_comp]

/-- 概要：join の可逆円柱上の族の両端は右図式を固定した関手圏の頂点として同型。
方針：円柱の射影はエピな普遍的同値なので固定図式上の同値の二つの左逆を比較する。
規約：X は quasicategory、右図式は p。
使われ方：Kerodon Lemma 4.6.4.25 の同型を保存する方向。 -/
lemma nonempty_fixedDiagramVertexIso_of_joinCylinder (A K X : SSet.{u}) [Quasicategory X]
    (p : K ⟶ X) (F : join (A ⊗ equivalenceInterval) K ⟶ X)
    (hF : joinInr (A ⊗ equivalenceInterval) K ≫ F = p) :
    Nonempty (VertexIso (X := vertexFiber ((pre (joinInr A K)).app X) (functorVertex p))
      (fixedDiagramVertex (joinInr A K) p
        (joinMap (equivalenceCylinderEndpoint A false) (𝟙 K) ≫ F)
        (by rw [← Category.assoc, joinInr_joinMap, Category.id_comp, hF]))
      (fixedDiagramVertex (joinInr A K) p
        (joinMap (equivalenceCylinderEndpoint A true) (𝟙 K) ≫ F)
        (by rw [← Category.assoc, joinInr_joinMap, Category.id_comp, hF]))) := by
  apply nonempty_fixedDiagramVertexIso_of_cylinder
    (joinInr A K) (joinInr (A ⊗ equivalenceInterval) K)
    (joinMap (fst A equivalenceInterval) (𝟙 K))
    (by rw [joinInr_joinMap, Category.id_comp])
    (isPrecompositionEquivalence_joinCylinderProjection A K)
    (joinMap (equivalenceCylinderEndpoint A false) (𝟙 K))
    (joinMap (equivalenceCylinderEndpoint A true) (𝟙 K))
    (by rw [joinInr_joinMap, Category.id_comp]) (by rw [joinInr_joinMap, Category.id_comp])
    (by rw [← joinMap_comp, equivalenceCylinderEndpoint_fst, Category.id_comp, joinMap_id])
    (by rw [← joinMap_comp, equivalenceCylinderEndpoint_fst, Category.id_comp, joinMap_id])
    p F hF

end SerrePositivity.InfinityCategories
