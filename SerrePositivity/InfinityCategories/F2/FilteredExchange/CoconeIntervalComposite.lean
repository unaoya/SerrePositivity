module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoconeFiberEvaluation

/-!
概要：元の余錐の単位の後に、任意の指定区間族の定値図式への作用を合成する。
方針：全 Hom に限定せず、同じ相対合成の座標式を任意のパラメータで使う。
規約：指定余錐と指定区間を保持。使われ方：余極限関手の元の指定辺による作用。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B T : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}}
  (c : JoinCocone F) {z : SpaceInfinity.{u} _⦋0⦌}
  (a : T ⟶ intervalMappingSpace c.vertex z)

/-- 元の余錐の単位と、同じ指定区間の定値図式への作用の全相対合成。 -/
def coconeIntervalRelativeComposite :=
  constantUnstraighteningComposite (leftUnstraighteningProjection F) c.vertex z
    ((SSet.const (coconeTransformationVertex c)) ≫
      leftUnstraighteningMappingSpaceMap F (SSet.const c.vertex))
    (constantDiagramTransformation B a ≫
      leftUnstraighteningMappingSpaceMap (SSet.const c.vertex : B ⟶ _) (SSet.const z))

/-- 任意の指定区間族の合成は、元の余錐の fiber 写像と元の底の二座標で計算できる。 -/
lemma coconeIntervalRelativeComposite_coordinates :
    uncurry (coconeIntervalRelativeComposite c a ≫
      (constantUnstraighteningRelativeIso (leftUnstraighteningProjection F) z).hom) =
      lift (lift (fst (leftUnstraightening F) T ≫ coconeFiberMap c)
        (fst (leftUnstraightening F) T ≫ leftUnstraighteningProjection F) ≫
          (constantPullbackFiberIso pointedSpaceProjection c.vertex).inv) (snd _ T) ≫
        uncurry ((constantDiagramTransformation B a ≫
          leftUnstraighteningMappingSpaceMap (SSet.const c.vertex : B ⟶ _) (SSet.const z)) ≫
          (constantUnstraighteningRelativeIso
            (leftUnstraighteningProjection (SSet.const c.vertex : B ⟶ _)) z).hom) := by
  rw [coconeIntervalRelativeComposite, constantUnstraighteningComposite_coordinates,
    Category.assoc]
  have h := coconeFiberMap_evaluation (T := T) c
  exact congrArg (fun q => lift (lift q
    (fst (leftUnstraightening F) T ≫ leftUnstraighteningProjection F) ≫
      (constantPullbackFiberIso pointedSpaceProjection c.vertex).inv) (snd _ T) ≫ _) h

end SerrePositivity.InfinityCategories.F2
