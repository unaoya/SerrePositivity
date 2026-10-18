module

public import SerrePositivity.InfinityCategories.Core.JoinCylinderFixedDiagram
public import SerrePositivity.InfinityCategories.Core.JoinEquivalenceFunctor
public import SerrePositivity.InfinityCategories.Core.FatJoinFixedDiagramComparison

/-!
概要：fatJoin の可逆円柱上の族の両端は固定図式上で同型。
方針：左因子の円柱の射影の普遍的同値性を fatJoin で保ち、二つの端点制限を比較する。
規約：右因子の図式を固定する。
使われ方：Kerodon Lemma 4.6.4.25 の slice の同型の保存。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：可逆円柱との fatJoin の射影は普遍的な前合成の同値条件を満たす。
方針：左因子の fatJoin が普遍的同値を保つことを使う。
規約：二つの因子は任意。
使われ方：Kerodon Lemma 4.6.4.25 の fatJoin の圏論的円柱。 -/
lemma isPrecompositionEquivalence_fatJoinCylinderProjection (A K : SSet.{u}) :
    IsPrecompositionEquivalence (fatJoinMap (fst A equivalenceInterval) (𝟙 K)) :=
  (isPrecompositionEquivalence_equivalenceCylinder_fst A).fatJoinMap_left K

/-- 概要：fatJoin の可逆円柱の射影はエピ射。
方針：false 端による厳密な切断を使う。
規約：両因子の非空性は不要。
使われ方：Kerodon §4.6.4 の前合成の単射性。 -/
instance fatJoinCylinderProjection_epi (A K : SSet.{u}) :
    Epi (fatJoinMap (fst A equivalenceInterval) (𝟙 K)) := by
  let a := fatJoinMap (equivalenceCylinderEndpoint A false) (𝟙 K)
  have ha : a ≫ fatJoinMap (fst A equivalenceInterval) (𝟙 K) = 𝟙 _ := by
    dsimp [a]
    rw [fatJoinMap_comp, equivalenceCylinderEndpoint_fst, Category.id_comp, fatJoinMap_id]
  constructor
  intro Y f g h
  calc
    f = (a ≫ fatJoinMap (fst A equivalenceInterval) (𝟙 K)) ≫ f := by rw [ha, Category.id_comp]
    _ = a ≫ (fatJoinMap (fst A equivalenceInterval) (𝟙 K) ≫ g) := by rw [Category.assoc, h]
    _ = g := by rw [← Category.assoc, ha, Category.id_comp]

/-- 概要：fatJoin の可逆円柱上の族の両端は右図式を固定した関手圏の頂点として同型。
方針：円柱の射影はエピな普遍的同値なので固定図式上の同値の二つの左逆を比較する。
規約：X は quasicategory、右図式は p。
使われ方：Kerodon Lemma 4.6.4.25 の同型を保存する方向。 -/
lemma nonempty_fixedDiagramVertexIso_of_fatJoinCylinder (A K X : SSet.{u}) [Quasicategory X]
    (p : K ⟶ X) (F : fatJoin (A ⊗ equivalenceInterval) K ⟶ X)
    (hF : fatJoinInr (A ⊗ equivalenceInterval) K ≫ F = p) :
    Nonempty (VertexIso (X := vertexFiber ((pre (fatJoinInr A K)).app X) (functorVertex p))
      (fixedDiagramVertex (fatJoinInr A K) p
        (fatJoinMap (equivalenceCylinderEndpoint A false) (𝟙 K) ≫ F)
        (by rw [← Category.assoc, fatJoinInr_map, Category.id_comp, hF]))
      (fixedDiagramVertex (fatJoinInr A K) p
        (fatJoinMap (equivalenceCylinderEndpoint A true) (𝟙 K) ≫ F)
        (by rw [← Category.assoc, fatJoinInr_map, Category.id_comp, hF]))) := by
  apply nonempty_fixedDiagramVertexIso_of_cylinder
    (fatJoinInr A K) (fatJoinInr (A ⊗ equivalenceInterval) K)
    (fatJoinMap (fst A equivalenceInterval) (𝟙 K))
    (by rw [fatJoinInr_map, Category.id_comp])
    (isPrecompositionEquivalence_fatJoinCylinderProjection A K)
    (fatJoinMap (equivalenceCylinderEndpoint A false) (𝟙 K))
    (fatJoinMap (equivalenceCylinderEndpoint A true) (𝟙 K))
    (by rw [fatJoinInr_map, Category.id_comp]) (by rw [fatJoinInr_map, Category.id_comp])
    (by rw [fatJoinMap_comp, equivalenceCylinderEndpoint_fst, Category.id_comp, fatJoinMap_id])
    (by rw [fatJoinMap_comp, equivalenceCylinderEndpoint_fst, Category.id_comp, fatJoinMap_id])
    p F hF

end SerrePositivity.InfinityCategories
