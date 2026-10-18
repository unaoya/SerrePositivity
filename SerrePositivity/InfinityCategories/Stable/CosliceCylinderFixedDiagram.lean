module
public import SerrePositivity.InfinityCategories.Stable.CosliceCylinderExtension
public import SerrePositivity.InfinityCategories.Core.JoinCylinderFixedDiagram
public import SerrePositivity.InfinityCategories.Core.JoinEquivalenceFunctor

/-! # 左図式を固定した可逆円柱の同型

概要：右因子の可逆円柱の両端は、左図式を固定した関手圏で同型である。
方針：円柱の射影の普遍的前合成同値性を join と fat join で保つ。
規約：左図式を厳密に固定する。使われ方：coslice の族の同型の保存。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：右因子の可逆円柱との join の射影は普遍的な前合成同値。
方針：右因子の join が同値を保つことを使う。
規約：因子は任意。使われ方：固定左図式の同型判定。 -/
lemma isPrecompositionEquivalence_joinRightCylinderProjection (A K : SSet.{u}) :
    IsPrecompositionEquivalence (joinMap (𝟙 K) (fst A equivalenceInterval)) :=
  (isPrecompositionEquivalence_equivalenceCylinder_fst A).joinMap_right K

/-- 概要：join の可逆円柱の射影はエピ射。
方針：false 端による厳密な切断を使う。
規約：両因子の非空性は不要。
使われ方：Kerodon §4.6.4 の前合成の単射性。 -/
instance joinRightCylinderProjection_epi (A K : SSet.{u}) :
    Epi (joinMap (𝟙 K) (fst A equivalenceInterval)) := by
  let a := joinMap (𝟙 K) (equivalenceCylinderEndpoint A false)
  have ha : a ≫ joinMap (𝟙 K) (fst A equivalenceInterval) = 𝟙 _ := by
    dsimp [a]
    rw [← joinMap_comp, equivalenceCylinderEndpoint_fst, Category.id_comp, joinMap_id]
  constructor
  intro Y f g h
  calc
    f = (a ≫ joinMap (𝟙 K) (fst A equivalenceInterval)) ≫ f := by rw [ha, Category.id_comp]
    _ = a ≫ (joinMap (𝟙 K) (fst A equivalenceInterval) ≫ g) := by rw [Category.assoc, h]
    _ = g := by rw [← Category.assoc, ha, Category.id_comp]

/-- 概要：join の可逆円柱上の族の両端は左図式を固定した関手圏の頂点として同型。
方針：円柱の射影はエピな普遍的同値なので固定図式上の同値の二つの左逆を比較する。
規約：X は quasicategory、左図式は p。
使われ方：Kerodon Lemma 4.6.4.25 の同型を保存する方向。 -/
lemma nonempty_fixedDiagramVertexIso_of_joinRightCylinder (A K X : SSet.{u}) [Quasicategory X]
    (p : K ⟶ X) (F : join K (A ⊗ equivalenceInterval) ⟶ X)
    (hF : joinInl K (A ⊗ equivalenceInterval) ≫ F = p) :
    Nonempty (VertexIso (X := vertexFiber ((pre (joinInl K A)).app X) (functorVertex p))
      (fixedDiagramVertex (joinInl K A) p
        (joinMap (𝟙 K) (equivalenceCylinderEndpoint A false) ≫ F)
        (by rw [← Category.assoc, joinInl_joinMap, Category.id_comp, hF]))
      (fixedDiagramVertex (joinInl K A) p
        (joinMap (𝟙 K) (equivalenceCylinderEndpoint A true) ≫ F)
        (by rw [← Category.assoc, joinInl_joinMap, Category.id_comp, hF]))) := by
  apply nonempty_fixedDiagramVertexIso_of_cylinder
    (joinInl K A) (joinInl K (A ⊗ equivalenceInterval))
    (joinMap (𝟙 K) (fst A equivalenceInterval))
    (by rw [joinInl_joinMap, Category.id_comp])
    (isPrecompositionEquivalence_joinRightCylinderProjection A K)
    (joinMap (𝟙 K) (equivalenceCylinderEndpoint A false))
    (joinMap (𝟙 K) (equivalenceCylinderEndpoint A true))
    (by rw [joinInl_joinMap, Category.id_comp]) (by rw [joinInl_joinMap, Category.id_comp])
    (by rw [← joinMap_comp, equivalenceCylinderEndpoint_fst, Category.id_comp, joinMap_id])
    (by rw [← joinMap_comp, equivalenceCylinderEndpoint_fst, Category.id_comp, joinMap_id])
    p F hF


/-- 概要：右因子の可逆円柱との fatJoin の射影は普遍的な前合成同値。
方針：右因子の fatJoin が同値を保つことを使う。
規約：因子は任意。使われ方：固定左図式の同型判定。 -/
lemma isPrecompositionEquivalence_fatJoinRightCylinderProjection (A K : SSet.{u}) :
    IsPrecompositionEquivalence (fatJoinMap (𝟙 K) (fst A equivalenceInterval)) :=
  (isPrecompositionEquivalence_equivalenceCylinder_fst A).fatJoinMap_right K

/-- 概要：fatJoin の可逆円柱の射影はエピ射。
方針：false 端による厳密な切断を使う。
規約：両因子の非空性は不要。
使われ方：Kerodon §4.6.4 の前合成の単射性。 -/
instance fatJoinRightCylinderProjection_epi (A K : SSet.{u}) :
    Epi (fatJoinMap (𝟙 K) (fst A equivalenceInterval)) := by
  let a := fatJoinMap (𝟙 K) (equivalenceCylinderEndpoint A false)
  have ha : a ≫ fatJoinMap (𝟙 K) (fst A equivalenceInterval) = 𝟙 _ := by
    dsimp [a]
    rw [fatJoinMap_comp, equivalenceCylinderEndpoint_fst, Category.id_comp, fatJoinMap_id]
  constructor
  intro Y f g h
  calc
    f = (a ≫ fatJoinMap (𝟙 K) (fst A equivalenceInterval)) ≫ f := by rw [ha, Category.id_comp]
    _ = a ≫ (fatJoinMap (𝟙 K) (fst A equivalenceInterval) ≫ g) := by rw [Category.assoc, h]
    _ = g := by rw [← Category.assoc, ha, Category.id_comp]

/-- 概要：fatJoin の可逆円柱上の族の両端は左図式を固定した関手圏の頂点として同型。
方針：円柱の射影はエピな普遍的同値なので固定図式上の同値の二つの左逆を比較する。
規約：X は quasicategory、左図式は p。
使われ方：Kerodon Lemma 4.6.4.25 の同型を保存する方向。 -/
lemma nonempty_fixedDiagramVertexIso_of_fatJoinRightCylinder (A K X : SSet.{u}) [Quasicategory X]
    (p : K ⟶ X) (F : fatJoin K (A ⊗ equivalenceInterval) ⟶ X)
    (hF : fatJoinInl K (A ⊗ equivalenceInterval) ≫ F = p) :
    Nonempty (VertexIso (X := vertexFiber ((pre (fatJoinInl K A)).app X) (functorVertex p))
      (fixedDiagramVertex (fatJoinInl K A) p
        (fatJoinMap (𝟙 K) (equivalenceCylinderEndpoint A false) ≫ F)
        (by rw [← Category.assoc, fatJoinInl_map, Category.id_comp, hF]))
      (fixedDiagramVertex (fatJoinInl K A) p
        (fatJoinMap (𝟙 K) (equivalenceCylinderEndpoint A true) ≫ F)
        (by rw [← Category.assoc, fatJoinInl_map, Category.id_comp, hF]))) := by
  apply nonempty_fixedDiagramVertexIso_of_cylinder
    (fatJoinInl K A) (fatJoinInl K (A ⊗ equivalenceInterval))
    (fatJoinMap (𝟙 K) (fst A equivalenceInterval))
    (by rw [fatJoinInl_map, Category.id_comp])
    (isPrecompositionEquivalence_fatJoinRightCylinderProjection A K)
    (fatJoinMap (𝟙 K) (equivalenceCylinderEndpoint A false))
    (fatJoinMap (𝟙 K) (equivalenceCylinderEndpoint A true))
    (by rw [fatJoinInl_map, Category.id_comp]) (by rw [fatJoinInl_map, Category.id_comp])
    (by rw [fatJoinMap_comp, equivalenceCylinderEndpoint_fst, Category.id_comp, fatJoinMap_id])
    (by rw [fatJoinMap_comp, equivalenceCylinderEndpoint_fst, Category.id_comp, fatJoinMap_id])
    p F hF


end SerrePositivity.InfinityCategories
