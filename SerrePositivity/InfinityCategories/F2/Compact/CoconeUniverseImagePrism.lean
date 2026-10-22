module

public import SerrePositivity.InfinityCategories.F2.Compact.CoconeUniverseImage
public import SerrePositivity.InfinityCategories.F2.Compact.UniverseCoconeCylinder

/-!
概要：宇宙変更後の元の余錐の標準 prism を、同じ元の全空間係数へ戻す。
方針：図式部分の実比較を前合成し、元の射影と join 円柱を厳密に照合する。
規約：同じ始点と同じ底を持つ元の二つの prism を比較する。
使われ方：元の指定 fiber 写像の全自然比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
variable {B : SSet.{u + 1}} [Quasicategory B] {F : B ⟶ SpaceInfinity.{u}}

/-- 元の余錐像の標準 prism を、元の全空間の同じ宇宙持ち上げへ制限する。 -/
def coconeUniverseImagePrism (c : JoinCocone F) :
    (Δ[1] : SSet.{u + 2}) ⊗ (SSet.uliftFunctor.{u + 2, u + 1}).obj
      (leftUnstraightening F) ⟶ PointedSpaceInfinity.{u + 1} :=
  (Δ[1] ◁ coconeUniverseSourceComparison c) ≫ coconeFiberPrism (coconeUniverseImage c)

/-- 二つ目の実 prism の始点も、同じ元の pointed 表現の制限そのもの。 -/
lemma coconeUniverseImagePrism_zero (c : JoinCocone F) :
    prismEndpoint 0 _ ≫ coconeUniverseImagePrism c =
      (spaceUniverseCoconeSourceRepresentation c).pointedMap := by
  rw [coconeUniverseImagePrism, ← Category.assoc, prismEndpoint_naturality,
    Category.assoc, coconeFiberPrism_zero, coconeUniverseSourceComparison_pointed]

/-- 二つ目の実 prism の終点は、元の余錐像の指定 fiber 写像そのものを保つ。 -/
lemma coconeUniverseImagePrism_one (c : JoinCocone F) :
    prismEndpoint 1 _ ≫ coconeUniverseImagePrism c =
      coconeUniverseSourceComparison c ≫ coconeFiberMap (coconeUniverseImage c) ≫
        vertexFiberι pointedSpaceProjection
          (spaceUniverseDiagram.app _ (ULift.up c.vertex)) := by
  rw [coconeUniverseImagePrism, ← Category.assoc, prismEndpoint_naturality,
    Category.assoc, coconeFiberPrism_one]
  rfl

/-- 元の二つの prism の底は、同じ元の join 円柱の宇宙変更として厳密に等しい。 -/
lemma coconeUniverseImagePrism_projection (c : JoinCocone F) :
    coconeUniverseImagePrism c ≫ pointedSpaceProjection =
      uliftSimplexPrism.{u + 1, u + 2} (coconeFiberBasePrism (F := F)) ≫
        (SSet.uliftFunctor.{u + 2, u + 1}).map c.val ≫ spaceUniverseDiagram.{u} := by
  rw [coconeUniverseImagePrism, Category.assoc, coconeFiberPrism_projection,
    coconeFiberBasePrism, coconeUniverseImage_val]
  simp only [← Category.assoc]
  rw [← whiskerLeft_comp, coconeUniverseSourceComparison_projection]
  rw [coconeFiberBasePrism, uliftSimplexPrism_precomp, uliftCoconeUnitCylinder]
  simp only [Category.assoc]

end SerrePositivity.InfinityCategories.F2.Compact
