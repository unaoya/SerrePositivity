module

public import SerrePositivity.InfinityCategories.F2.ConstantUnstraighteningEvaluation
public import SerrePositivity.InfinityCategories.F2.ConstantDiagramTransportWitness
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningMappingInvertible

/-!
概要：定値標的比較の指定頂点を実際の全空間射と fiber の射影で表示する。
方針：相対評価を全単体で計算する。
規約：元の射を保持。使われ方：coherent 三角形の長辺と単位の実際の値の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：定値標的の相対頂点の値は元の射と fiber 射影の合成の頂点。
方針：全入力を評価。規約：厳密な等式。使われ方：元の長辺の値の照合。 -/
lemma constantUnstraighteningRelativeIso_vertex {A B : SSet.{u + 1}}
    (a : A ⟶ B) (z : SpaceInfinity.{u} _⦋0⦌)
    (f : A ⟶ leftUnstraightening (SSet.const z : B ⟶ SpaceInfinity))
    (hf : f ≫ leftUnstraighteningProjection (SSet.const z) = a) :
    (constantUnstraighteningRelativeIso a z).hom.app (Opposite.op ⦋0⦌)
      (relativeFunctorVertex (leftUnstraighteningProjection (SSet.const z)) a f hf) =
        functorVertex (f ≫ constantUnstraighteningFiberProjection B z) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro n α
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 概要：元の定値標的比較の頂点は元の全空間射から値への実際の合成。
方針：相対頂点の厳密な回収と fiber 座標の計算。
規約：元の変換を保持。使われ方：単位との三角形の比較。 -/
lemma coherentConstantTargetMap_vertex {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (z : SpaceInfinity.{u} _⦋0⦌)
    (t : (leftUnstraighteningTransformationSpace F (SSet.const z)) _⦋0⦌) :
    (coherentConstantTargetMap F z).app (Opposite.op ⦋0⦌) t =
      functorVertex ((leftUnstraighteningMappingVertexMap F (SSet.const z) t).val ≫
        constantUnstraighteningFiberProjection B z ≫
          (pointedSpaceFiberValueEquivalence z).hom) := by
  have h := constantUnstraighteningRelativeIso_vertex (leftUnstraighteningProjection F) z
    (leftUnstraighteningMappingVertexMap F (SSet.const z) t).val
    (leftUnstraighteningMappingVertexMap F (SSet.const z) t).property
  have h' := congrArg (fun v : ((ihom (leftUnstraightening F)).obj
      (vertexFiber pointedSpaceProjection z)) _⦋0⦌ =>
    ((ihom (leftUnstraightening F)).map
      (pointedSpaceFiberValueEquivalence z).hom).app (Opposite.op ⦋0⦌) v) h
  rw [leftUnstraighteningMappingVertexMap_vertex F (SSet.const z) t] at h'
  exact h'

end SerrePositivity.InfinityCategories.F2
