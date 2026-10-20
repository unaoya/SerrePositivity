module

public import SerrePositivity.InfinityCategories.F2.ConstantUnstraighteningComposition
public import SerrePositivity.InfinityCategories.F2.CoconePointHomComposition
public import SerrePositivity.InfinityCategories.Core.ConeFamily
public import SerrePositivity.InfinityCategories.Core.EquivalencePath

/-!
概要：元の余錐の全空間から fiber への実際の写像を取り出し、全 Hom の相対合成を評価する。
方針：標準比較の元の頂点を内部 Hom の射へ戻し、その定値族を評価する。
規約：余錐も比較も選び直さない。
使われ方：元の単位の前合成による全 Hom の比較への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}}

/-- 概要：元の余錐の標準比較が定める全空間から指定頂点の fiber への実際の射。
方針：元の変換頂点の比較の像を内部 Hom の射へ戻す。
規約：元の比較の像そのもの。使われ方：相対合成の第一因子の評価。 -/
def coconeFiberMap (c : JoinCocone F) :
    leftUnstraightening F ⟶ vertexFiber pointedSpaceProjection c.vertex :=
  (functorVertexEquiv _ _).symm
    ((leftUnstraighteningMappingSpaceMap F (SSet.const c.vertex) ≫
      (constantUnstraighteningRelativeIso (leftUnstraighteningProjection F) c.vertex).hom).app
        (Opposite.op ⦋0⦌) (coconeTransformationVertex c))

/-- 概要：取り出した fiber 写像の頂点は元の比較の像そのもの。
方針：内部 Hom の頂点と射の全単射の往復。
規約：厳密な式。使われ方：定値族の全パラメータ評価。 -/
lemma coconeFiberMap_vertex (c : JoinCocone F) :
    functorVertex (coconeFiberMap c) =
      (leftUnstraighteningMappingSpaceMap F (SSet.const c.vertex) ≫
        (constantUnstraighteningRelativeIso (leftUnstraighteningProjection F) c.vertex).hom).app
          (Opposite.op ⦋0⦌) (coconeTransformationVertex c) :=
  (functorVertexEquiv _ _).apply_symm_apply _

/-- 概要：元の余錐の定値変換の比較は実際の fiber 写像の定値族として評価できる。
方針：定値射の後合成の式と関手頂点の uncurry の式を使う。
規約：任意の全パラメータ。使われ方：全 Hom の第一因子の簡約。 -/
lemma coconeFiberMap_evaluation {T : SSet.{u + 1}} (c : JoinCocone F) :
    uncurry ((SSet.const (coconeTransformationVertex c) :
      T ⟶ leftUnstraighteningTransformationSpace F (SSet.const c.vertex)) ≫
      leftUnstraighteningMappingSpaceMap F (SSet.const c.vertex) ≫
        (constantUnstraighteningRelativeIso (leftUnstraighteningProjection F) c.vertex).hom) =
      fst (leftUnstraightening F) T ≫ coconeFiberMap c := by
  have h := coconeFiberMap_vertex c
  have e := congrArg (fun v : ((ihom (leftUnstraightening F)).obj
      (vertexFiber pointedSpaceProjection c.vertex)) _⦋0⦌ ↦
        uncurry (SSet.const v : T ⟶ _)) h.symm
  rw [SSet.const_comp]
  exact e.trans (uncurry_const_functorVertex (coconeFiberMap c))

/-- 概要：元の全 Hom の相対合成を指定余錐の fiber 写像と元の底の射影から評価する。
方針：相対合成の二座標の式で第一因子の定値族を簡約する。
規約：元の全 Hom の全高次パラメータ。使われ方：定値 fiber の作用との整合。 -/
lemma coconePointHomRelativeComposite_coordinates (c : JoinCocone F)
    (z : SpaceInfinity.{u} _⦋0⦌) :
    uncurry (coconePointHomRelativeComposite c z ≫
      (constantUnstraighteningRelativeIso (leftUnstraighteningProjection F) z).hom) =
        lift (lift (fst (leftUnstraightening F) (pinchedHomLeft c.vertex z) ≫ coconeFiberMap c)
          (fst (leftUnstraightening F) (pinchedHomLeft c.vertex z) ≫
            leftUnstraighteningProjection F) ≫
              (constantPullbackFiberIso pointedSpaceProjection c.vertex).inv)
          (snd (leftUnstraightening F) (pinchedHomLeft c.vertex z)) ≫
            uncurry ((coconePointHomSecondTransformation c z ≫
              leftUnstraighteningMappingSpaceMap (SSet.const c.vertex) (SSet.const z : B ⟶ _)) ≫
                (constantUnstraighteningRelativeIso
                  (leftUnstraighteningProjection (SSet.const c.vertex : B ⟶ _)) z).hom) := by
  change uncurry (constantUnstraighteningComposite _ _ _ _ _ ≫ _) = _
  rw [constantUnstraighteningComposite_coordinates, Category.assoc]
  have h := coconeFiberMap_evaluation (T := pinchedHomLeft c.vertex z) c
  exact congrArg (fun q ↦ lift (lift q
    (fst (leftUnstraightening F) (pinchedHomLeft c.vertex z) ≫ leftUnstraighteningProjection F) ≫
      (constantPullbackFiberIso pointedSpaceProjection c.vertex).inv)
        (snd (leftUnstraightening F) (pinchedHomLeft c.vertex z)) ≫ _) h

end SerrePositivity.InfinityCategories.F2
