module

public import SerrePositivity.InfinityCategories.F1.Coherent.TransformationFamilyNaturality
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningTransformationFamily

/-!
概要：変換空間への射を指定両端の区間上の図式へ戻し厳密に回収する。
方針：普遍的な prism の評価の結合子を逆にたどる。
規約：変換のパラメーターを全て保持する。
使われ方：pointed な実現の一意性を変換空間への射の一意性へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：端点包含を結合子の逆で移すと元の端点包含の積。
方針：次数ごとの三成分を計算する。
規約：任意の端点に適用する。
使われ方：区間付き図式の端点条件。 -/
lemma prismEndpoint_associator_inv (i : Fin 2) (B K : SSet.{u}) :
    prismEndpoint i (B ⊗ K) ≫ (α_ (Δ[1] : SSet.{u}) B K).inv = prismEndpoint i B ▷ K := by
  apply SSet.hom_ext
  intro n
  rfl

/-- 概要：coherent な変換の族を区間付きの積の底上の図式へ戻す。
方針：普遍評価の prism の結合を変更する。
規約：底とパラメーターは任意。
使われ方：相対射を表す二つの変換の族の比較。 -/
def coherentTransformationFamilyDiagram {B K : SSet.{u + 1}}
    {F G : B ⟶ SpaceInfinity.{u}} (t : K ⟶ leftUnstraighteningTransformationSpace F G) :
    (Δ[1] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ SpaceInfinity.{u} :=
  (α_ Δ[1] B K).inv ≫ functorParameterizedPrism (intervalMappingUncurry t)

/-- 概要：変換の族から戻した図式の零端は元の始域図式。
方針：区間模型の零端条件を評価する。
規約：パラメーターに定値な図式。
使われ方：表現の積の零端との整合性。 -/
lemma coherentTransformationFamilyDiagram_zero {B K : SSet.{u + 1}}
    {F G : B ⟶ SpaceInfinity.{u}} (t : K ⟶ leftUnstraighteningTransformationSpace F G) :
    prismEndpoint 0 (B ⊗ K) ≫ coherentTransformationFamilyDiagram t = fst B K ≫ F := by
  rw [coherentTransformationFamilyDiagram, ← Category.assoc, prismEndpoint_associator_inv]
  exact functorParameterizedPrism_vertex_of_const 1 _ 0 F (intervalMappingUncurry_zero t)

/-- 概要：変換の族から戻した図式の一端は元の終域図式。
方針：区間模型の一端条件を評価する。
規約：パラメーターに定値な図式。
使われ方：表現の積の一端との整合性。 -/
lemma coherentTransformationFamilyDiagram_one {B K : SSet.{u + 1}}
    {F G : B ⟶ SpaceInfinity.{u}} (t : K ⟶ leftUnstraighteningTransformationSpace F G) :
    prismEndpoint 1 (B ⊗ K) ≫ coherentTransformationFamilyDiagram t = fst B K ≫ G := by
  rw [coherentTransformationFamilyDiagram, ← Category.assoc, prismEndpoint_associator_inv]
  exact functorParameterizedPrism_vertex_of_const 1 _ 1 G (intervalMappingUncurry_one t)

/-- 概要：変換の族から図式へ戻して再び curry すると元の射。
方針：区間模型と prism の評価の単射性を使う。
規約：厳密な射の等式。
使われ方：同型までの実現の一意性を元の変換の族へ戻す。 -/
lemma coherentTransformationFamilyDiagram_curry {B K : SSet.{u + 1}}
    {F G : B ⟶ SpaceInfinity.{u}} (t : K ⟶ leftUnstraighteningTransformationSpace F G) :
    coherentTransformationFamilyCurry F G (coherentTransformationFamilyDiagram t)
      (coherentTransformationFamilyDiagram_zero t)
      (coherentTransformationFamilyDiagram_one t) = t := by
  apply intervalMappingUncurry_injective (functorVertex F) (functorVertex G)
  apply functorParameterizedPrism_injective
  rw [coherentTransformationFamilyCurry_prism, coherentTransformationFamilyDiagram]
  simp only [Iso.hom_inv_id_assoc]

end SerrePositivity.InfinityCategories
