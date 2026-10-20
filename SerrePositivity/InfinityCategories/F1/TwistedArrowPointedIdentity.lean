module

public import SerrePositivity.InfinityCategories.F1.TwistedArrowPointedDisplayFiber

/-!
概要：c1 の評価に用いる同じ恒等点は、始点固定の Tw の恒等点の pointed 比較による像。
方針：縮小した unstraightening の第一射影の自然性と、fiber 同型の包含の式を使う。
規約：pointed-space 全空間内の実際の点の厳密な等式を保持する。
使われ方：Tw の輸送を送った族と、c1 の普遍輸送の族の同じ初期値を照合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

local instance {C : SSet.{u}} [Quasicategory C] : Quasicategory (C.op ⊗ C) :=
  quasicategory_of_innerFibration (fst C.op C)

/-- 小さい unstraightening の全空間を持ち上げ、元の pointed 成分を取る。 -/
def smallLeftUnstraighteningPointedMap {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (smallLeftUnstraightening F) ⟶ PointedSpaceInfinity.{u} :=
  (smallLeftUnstraighteningIso F).hom ≫ pullback.fst pointedSpaceProjection F

/-- 小さい unstraightening の底変換は、同じ pointed 成分を厳密に保つ。 -/
lemma smallLeftUnstraighteningPointedMap_naturality {B D : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (G : (SSet.uliftFunctor.{u + 1, u}).obj D ⟶ SpaceInfinity.{u})
    (α : B ⟶ D) (h : (SSet.uliftFunctor.{u + 1, u}).map α ≫ G = F) :
    (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningMap F G α h) ≫
      smallLeftUnstraighteningPointedMap G = smallLeftUnstraighteningPointedMap F := by
  rw [smallLeftUnstraighteningPointedMap, ← Category.assoc,
    smallLeftUnstraighteningMap_naturality, Category.assoc, leftUnstraighteningMap_pointed]
  rfl

/-- 同じ指定 fiber の点を二つの同型で pointed-space へ送ると、元の全空間の第一射影に等しい。 -/
lemma smallLeftUnstraighteningPointedMap_fiber_point {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌)
    (v : (vertexFiber (smallLeftUnstraighteningProjection F) b) _⦋0⦌) :
    ((leftUnstraighteningFiberIso F (ULift.up b)).hom.app (Opposite.op ⦋0⦌)
      ((smallLeftUnstraighteningFiberIso F b).hom.app (Opposite.op ⦋0⦌) (ULift.up v))).val =
    (smallLeftUnstraighteningPointedMap F).app (Opposite.op ⦋0⦌) (ULift.up v.val) := by
  have h : (smallLeftUnstraighteningFiberIso F b).hom ≫
      (leftUnstraighteningFiberIso F (ULift.up b)).hom ≫
      vertexFiberι pointedSpaceProjection (F.app (Opposite.op ⦋0⦌) (ULift.up b)) =
      (SSet.uliftFunctor.{u + 1, u}).map
        (vertexFiberι (smallLeftUnstraighteningProjection F) b) ≫
      smallLeftUnstraighteningPointedMap F := by
    rw [leftUnstraighteningFiberIso_hom_ι,
      ← Category.assoc, smallLeftUnstraighteningFiberIso_hom_ι]
    rfl
  exact congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) (ULift.up v)) h

/-- c1 の同じ恒等点は、始点固定の Tw の恒等点を同じ全体の pointed 比較で送った点そのもの。 -/
lemma canonicalYonedaPointedIdentity_eq_sourceDisplay {C : SSet.{u}} [Quasicategory C]
    (x : C _⦋0⦌) :
    (canonicalYonedaPointedIdentity x).val =
    (twistedArrowSourcePointedDisplay x).app (Opposite.op ⦋0⦌)
      (ULift.up (twistedArrowSourceIdentity x)) := by
  let R := representablePresheafInfinity x
  let H := twistedArrowHomInfinity C
  let α := twistedArrowTargetInclusion x
  let h := (representablePresheafInfinity_eq_targetRestriction x).symm
  calc
    _ = (smallLeftUnstraighteningPointedMap R).app (Opposite.op ⦋0⦌)
        (ULift.up (canonicalYonedaUnstraighteningIdentity x)) :=
      smallLeftUnstraighteningPointedMap_fiber_point R _ (canonicalYonedaIdentityFiber x)
    _ = ((SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningMap R H α h) ≫
        smallLeftUnstraighteningPointedMap H).app (Opposite.op ⦋0⦌)
          (ULift.up (canonicalYonedaUnstraighteningIdentity x)) :=
      congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌)
        (ULift.up (canonicalYonedaUnstraighteningIdentity x)))
        (smallLeftUnstraighteningPointedMap_naturality R H α h).symm
    _ = (smallLeftUnstraighteningPointedMap H).app (Opposite.op ⦋0⦌)
        (ULift.up ((leftStraighteningInfinityReconstruction (twistedArrowProjection C)).app
          (Opposite.op ⦋0⦌) ((pullback.fst (twistedArrowProjection C)
            (twistedArrowSourceInclusion x)).app (Opposite.op ⦋0⦌)
              (twistedArrowSourceIdentity x)))) :=
      congrArg (fun v ↦ (smallLeftUnstraighteningPointedMap H).app
        (Opposite.op ⦋0⦌) (ULift.up v))
        (canonicalYonedaUnstraighteningIdentity_global_source x)
    _ = _ := rfl

end SerrePositivity.InfinityCategories
