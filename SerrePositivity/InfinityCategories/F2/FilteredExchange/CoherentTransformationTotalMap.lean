module

public import SerrePositivity.InfinityCategories.F1.SmallLeftUnstraighteningOverMap
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningMappingInvertible

/-!
概要：元の coherent 変換の全空間作用を元の小さい宇宙へ移す。
方針：写像空間比較の指定頂点の射を縮小し、同じ縮小同型との自然性を保持する。
規約：元の変換を変更しない。使われ方：標的の単位との合成を具体的 Kan 射へ接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (t : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)

/-- 概要：元の変換の指定全空間作用を小さい全空間間の射として表示。
方針：同じ指定射を縮小。規約：元の作用を保持。使われ方：余極限頂点間の具体的射。 -/
def coherentTransformationTotalMap : smallLeftUnstraightening F ⟶ smallLeftUnstraightening G :=
  smallLeftUnstraighteningOverMap F G (leftUnstraighteningMappingVertexMap F G t).val

/-- 概要：元の変換の小さい全空間射は元の底を厳密に保つ。
方針：指定射の底の条件を縮小。
規約：射の厳密な等式。使われ方：元の fiber ごとの射の照合。 -/
lemma coherentTransformationTotalMap_projection :
    coherentTransformationTotalMap F G t ≫ smallLeftUnstraighteningProjection G =
      smallLeftUnstraighteningProjection F :=
  smallLeftUnstraighteningOverMap_projection F G _
    (leftUnstraighteningMappingVertexMap F G t).property

/-- 概要：小さい全空間射の持ち上げは元の指定作用と縮小同型を介して一致。
方針：縮小の元の自然性。規約：実際の射。使われ方：元の単位の比較への移送。 -/
lemma coherentTransformationTotalMap_lift :
    (smallLeftUnstraighteningIso F).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (coherentTransformationTotalMap F G t) =
        (leftUnstraighteningMappingVertexMap F G t).val ≫ (smallLeftUnstraighteningIso G).inv := by
  unfold coherentTransformationTotalMap
  apply (cancel_mono (smallLeftUnstraighteningIso G).hom).1
  rw [Category.assoc, smallLeftUnstraighteningOverMap_naturality]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.F2
