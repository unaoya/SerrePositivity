module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTransformationCospanCone
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTransformationTriangleRelative
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeVertexIsoHomotopy

/-!
概要：元の cospan 錐の二三角形の可換 path を底を固定する相対空間内で保持する。
方針：共通長辺を介する指定相対同型を作り、同じ相対空間内で円柱を選ぶ。
規約：全時刻で底を固定。使われ方：fiberwise interval 引き戻し模型への実際の比較射。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z)
local notation "cl" => coherentTransformationTotalMap F X C.toLeft
local notation "cr" => coherentTransformationTotalMap F Y C.toRight
local notation "cf" => coherentTransformationTotalMap X Z C.fromLeft
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight

/-- 概要：元の左右三角形からの底上の指定可換同型。
方針：相対写像空間内で共通の長辺を通る。
規約：元の二三角形を保持。使われ方：底を固定した全円柱の代表。 -/
def coherentCospanConeRelativePathIso :
    VertexIso (X := relativeFunctorSpace (smallLeftUnstraighteningProjection Z)
      (smallLeftUnstraighteningProjection F))
      (relativeFunctorVertex _ _ (cl ≫ cf)
        (by rw [Category.assoc, coherentTransformationTotalMap_projection,
          coherentTransformationTotalMap_projection]))
      (relativeFunctorVertex _ _ (cr ≫ cg)
        (by rw [Category.assoc, coherentTransformationTotalMap_projection,
          coherentTransformationTotalMap_projection])) :=
  (coherentTransformationTriangleRelativeIso F X Z C.toLeft C.fromLeft C.leftTriangle).symm ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk
      (congrArg (coherentTransformationRelativeVertex F Z) C.diagonal_eq)) ≪≫
        coherentTransformationTriangleRelativeIso F Y Z C.toRight C.fromRight C.rightTriangle

/-- 概要：元の相対可換同型を表す円柱・底固定式・元の類の一致の全データ。
方針：相対写像空間内での辺の実現。
規約：全単体・全時刻を保持。使われ方：底上の path 置換への入力。 -/
def coherentCospanConeRelativePathData :=
  relativeVertexIsoHomotopy (smallLeftUnstraighteningProjection Z)
    (smallLeftUnstraighteningProjection F)
    (by rw [Category.assoc, coherentTransformationTotalMap_projection,
      coherentTransformationTotalMap_projection])
    (by rw [Category.assoc, coherentTransformationTotalMap_projection,
      coherentTransformationTotalMap_projection]) (coherentCospanConeRelativePathIso F X Y Z C)

/-- 概要：元の cospan の底を固定した指定可換円柱。
方針：全データから元の円柱を取る。
規約：相対空間内で選択済み。使われ方：fiberwise 引き戻し比較の全 path。 -/
def coherentCospanConeRelativePathHomotopy : SSet.Homotopy (cl ≫ cf) (cr ≫ cg) :=
  (coherentCospanConeRelativePathData F X Y Z C).val

/-- 概要：元の可換円柱は底への射影が全時刻で厳密に定値。
方針：相対空間内での実現の底の式。
規約：全円柱の等式。使われ方：fiberwise interval family への因子分解。 -/
lemma coherentCospanConeRelativePathHomotopy_projection :
    (coherentCospanConeRelativePathHomotopy F X Y Z C).h ≫
      smallLeftUnstraighteningProjection Z =
        fst (smallLeftUnstraightening F) (Δ[1] : SSet.{u}) ≫ smallLeftUnstraighteningProjection F :=
  (coherentCospanConeRelativePathData F X Y Z C).property.1

/-- 概要：選択した底固定円柱の類は元の相対可換同型の忘却像。
方針：相対空間の辺の代表の仕様。
規約：元の類を保持。使われ方：以前の全空間比較との指定値の照合。 -/
lemma coherentCospanConeRelativePathHomotopy_hom :
    SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (coherentCospanConeRelativePathHomotopy F X Y Z C)) =
        ((coherentCospanConeRelativePathIso F X Y Z C).map
          (vertexFiberι ((ihom (smallLeftUnstraightening F)).map
            (smallLeftUnstraighteningProjection Z))
              (functorVertex (smallLeftUnstraighteningProjection F)))).hom :=
  (coherentCospanConeRelativePathData F X Y Z C).property.2

end SerrePositivity.InfinityCategories.F2
