module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanPointedConeLift
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTransformationTotalMap

/-!
概要：元の fiber 射と pointed 始点族の合成を、縮小前の実際の全空間作用へ同定する。
方針：fiber の包含式と縮小同型の自然性を使う。
規約：元の指定変換の作用射を保持。使われ方：native 三角形の中間頂点の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌) (b : B _⦋0⦌)
local notation "pF" => smallLeftUnstraighteningProjection F
local notation "pG" => smallLeftUnstraighteningProjection G
local notation "f" => coherentTransformationTotalMap F G x
local notation "hf" => coherentTransformationTotalMap_projection F G x
local notation "m" => smallUnstraighteningSourceRestriction F (vertexFiberι pF b)

/-- 小さい fiber 射は、縮小前の全空間への元の包含とも厳密に可換。 -/
lemma coherentFiberSourceRestriction_naturality :
    (SSet.uliftFunctor.{u + 1, u}).map (vertexFiberMap pF pG f hf b) ≫
        (smallUnstraighteningSourceRestriction G (vertexFiberι pG b)).left =
      (m).left ≫ (leftUnstraighteningMappingVertexMap F G x).val := by
  change (SSet.uliftFunctor.{u + 1, u}).map (vertexFiberMap pF pG f hf b) ≫
    ((SSet.uliftFunctor.{u + 1, u}).map (vertexFiberι pG b) ≫
      (smallLeftUnstraighteningIso G).hom) = _
  rw [← Category.assoc, ← Functor.map_comp, vertexFiberMap_ι,
    Functor.map_comp, Category.assoc]
  change (SSet.uliftFunctor.{u + 1, u}).map (vertexFiberι pF b) ≫
    (SSet.uliftFunctor.{u + 1, u}).map
      (smallLeftUnstraighteningOverMap F G (leftUnstraighteningMappingVertexMap F G x).val) ≫
      (smallLeftUnstraighteningIso G).hom = _
  rw [smallLeftUnstraighteningOverMap_naturality]
  rfl

/-- 実際の小さい fiber 射を持ち上げて pointed 始点族へ写すと、元の全空間作用に等しい。 -/
lemma coherentFiberPointedSource_naturality :
    (SSet.uliftFunctor.{u + 1, u}).map (vertexFiberMap pF pG f hf b) ≫
        coherentCospanFiberPointedSource G b =
      (m).left ≫ (leftUnstraighteningMappingVertexMap F G x).val ≫
        pullback.fst pointedSpaceProjection G := by
  change (SSet.uliftFunctor.{u + 1, u}).map (vertexFiberMap pF pG f hf b) ≫
    ((SSet.uliftFunctor.{u + 1, u}).map (vertexFiberι pG b) ≫
      (smallLeftUnstraighteningIso G).hom) ≫ pullback.fst pointedSpaceProjection G = _
  rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, vertexFiberMap_ι,
    Functor.map_comp, Category.assoc]
  change ((SSet.uliftFunctor.{u + 1, u}).map (vertexFiberι pF b) ≫
    (SSet.uliftFunctor.{u + 1, u}).map
      (smallLeftUnstraighteningOverMap F G (leftUnstraighteningMappingVertexMap F G x).val) ≫
      (smallLeftUnstraighteningIso G).hom) ≫ pullback.fst pointedSpaceProjection G = _
  rw [smallLeftUnstraighteningOverMap_naturality]
  rfl

end SerrePositivity.InfinityCategories.F2
