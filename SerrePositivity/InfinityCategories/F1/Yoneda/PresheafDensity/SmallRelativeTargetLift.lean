module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraighteningMappingSpace
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPostLaws

/-!
概要：任意の小さい始域から小さい unstraightening への相対射を元の全空間へ移す。
方針：相対 Hom の宇宙持ち上げと、標的の縮小同型の後合成を続ける。
規約：元の底の図式と全ての相対変換を保つ。
使われ方：元の密度大域評価との相対同型の持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {A B : SSet.{u}}
  (G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (a : A ⟶ B)

/-- 同じ相対 Hom の全族を、元の大きい標的全空間へ移す。 -/
def smallRelativeTargetLift :
    (SSet.uliftFunctor.{u + 1, u}).obj
      (relativeFunctorSpace (smallLeftUnstraighteningProjection G) a) ⟶
    relativeFunctorSpace (leftUnstraighteningProjection G)
      ((SSet.uliftFunctor.{u + 1, u}).map a) :=
  uliftRelativeFunctorMap (smallLeftUnstraighteningProjection G) a ≫
    HomotopyLimits.relativeFunctorPost
      ((SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection G))
      (leftUnstraighteningProjection G) (smallLeftUnstraighteningIso G).hom
      (smallLeftUnstraighteningIso_projection G) ((SSet.uliftFunctor.{u + 1, u}).map a)

/-- 全族の持ち上げは、同じ指定射を持ち上げて全空間の比較を続けた射の頂点。 -/
lemma smallRelativeTargetLift_vertex (f : A ⟶ smallLeftUnstraightening G)
    (hf : f ≫ smallLeftUnstraighteningProjection G = a) :
    (smallRelativeTargetLift G a).app (Opposite.op ⦋0⦌)
      (ULift.up (relativeFunctorVertex (smallLeftUnstraighteningProjection G) a f hf)) =
    relativeFunctorVertex (leftUnstraighteningProjection G)
      ((SSet.uliftFunctor.{u + 1, u}).map a)
      ((SSet.uliftFunctor.{u + 1, u}).map f ≫ (smallLeftUnstraighteningIso G).hom) (by
        rw [Category.assoc, smallLeftUnstraighteningIso_projection, ← Functor.map_comp, hf]) := by
  change (HomotopyLimits.relativeFunctorPost _ _ _
    (smallLeftUnstraighteningIso_projection G) _).app _
    ((uliftRelativeFunctorMap _ _).app _ (ULift.up (relativeFunctorVertex _ _ f hf))) = _
  rw [uliftRelativeFunctorMap_vertex, relativeFunctorPost_vertex]

end SerrePositivity.InfinityCategories.F2.Ind
