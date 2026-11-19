module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallUnstraighteningPointAction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraighteningBaseChange

/-!
概要：小さい unstraightening の底変換は、同じ fiber の頂点の pointed 表示を保つ。
方針：二つの fiber の同型を元の全空間へ含め、第一射影を比較する。
使われ方：指定した離散前層の射の密度の脚への作用。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

private theorem smallPointedImage_val
    {B : SSet.{u}} (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (b : B _⦋0⦌) (s : (vertexFiber (smallLeftUnstraighteningProjection F) b) _⦋0⦌) :
    (smallUnstraighteningPointedImage F b s).val =
      ((smallLeftUnstraighteningIso F).hom ≫ pullback.fst pointedSpaceProjection F).app
        (Opposite.op ⦋0⦌) (ULift.up s.val) := by
  let U := SSet.uliftFunctor.{u + 1, u}
  let h := (smallLeftUnstraighteningFiberIso F b).hom
  let k := (leftUnstraighteningFiberIso F (ULift.up b)).hom
  let t := vertexFiberι pointedSpaceProjection (F.app _ (ULift.up b))
  have hc : h ≫ k ≫ t = U.map (vertexFiberι (smallLeftUnstraighteningProjection F) b) ≫
       (smallLeftUnstraighteningIso F).hom ≫ pullback.fst pointedSpaceProjection F := by
    rw [leftUnstraighteningFiberIso_hom_ι, ← Category.assoc h,
      smallLeftUnstraighteningFiberIso_hom_ι, Category.assoc]
  exact congrArg (fun m => m.app (Opposite.op ⦋0⦌) (ULift.up s)) hc

/-- 小さい unstraightening の底変換は、同じ fiber の頂点の pointed 表示を保つ。
Kerodon Remark 5.6.2.18（Tag 0271）の頂点における底変換の法則。 -/
lemma smallUnstraighteningPointedImage_baseMap
    {B D : SSet.{u}} (i : B ⟶ D)
    (G : (SSet.uliftFunctor.{u + 1, u}).obj D ⟶ SpaceInfinity.{u})
    (b : B _⦋0⦌) :
    let U := SSet.uliftFunctor.{u + 1, u}
    let F := U.map i ≫ G
    let f := smallLeftUnstraighteningMap F G i rfl
    let d := i.app (Opposite.op ⦋0⦌) b
    ∀ (s : (vertexFiber (smallLeftUnstraighteningProjection F) b) _⦋0⦌),
    let t : (vertexFiber (smallLeftUnstraighteningProjection G) d) _⦋0⦌ :=
      ⟨f.app (Opposite.op ⦋0⦌) s.val, by
        have h : f ≫ smallLeftUnstraighteningProjection G =
            smallLeftUnstraighteningProjection F ≫ i :=
          smallLeftUnstraighteningMap_projection F G i rfl
        exact (congrArg (fun k => k.app (Opposite.op ⦋0⦌) s.val) h).trans
          ((congrArg (fun y => i.app (Opposite.op ⦋0⦌) y)
            (s.property.trans (pinchedConstant_zero b))).trans (pinchedConstant_zero d).symm)⟩
    smallUnstraighteningPointedImage F b s = smallUnstraighteningPointedImage G d t := by
  intro U F f d s t
  apply Subtype.ext
  rw [smallPointedImage_val, smallPointedImage_val]
  have h : U.map f ≫ (smallLeftUnstraighteningIso G).hom ≫ pullback.fst pointedSpaceProjection G =
      (smallLeftUnstraighteningIso F).hom ≫ pullback.fst pointedSpaceProjection F := by
    rw [← Category.assoc (U.map f), smallLeftUnstraighteningMap_naturality,
      Category.assoc, leftUnstraighteningMap_pointed]
  exact (congrArg (fun k => k.app (Opposite.op ⦋0⦌) (ULift.up s.val)) h).symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
