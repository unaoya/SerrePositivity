module
public import SerrePositivity.InfinityCategories.Derived.DGModuleUnitPinchedModel
public import SerrePositivity.InfinityCategories.Derived.DGModuleHomSpaceInfinity
/-!
概要：全 dg R 加群の生の nerve から、R を始域とする写像空間の全 ∞ 関手を作る。
方針：実二変数 Hom を R の代表加群に制限し、実 Yoneda 比較で各値を照合する。
規約：元の出力の射影性を仮定しない。使われ方：実 augmentation の空間値への移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v)
/-- 全 dg R 加群から R を始域とする写像空間への、全単体を保持する ∞ 関手。 -/
def dgHomUnderlyingSpaceInfinity :
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (dgHomModuleNerve R D) ⟶ SpaceInfinity.{max (u + 1) v} :=
  CartesianMonoidalCategory.lift
    (SSet.const (ULift.up (SSet.opObjEquiv.symm (dgHomModuleUnitVertex R D))))
    (𝟙 _) ≫ homInfinityJointEvaluation (dgHomModuleNerve R D)
/-- 同じ空間値関手の頂点値は、同じ Hom 関手の共同評価。 -/
lemma dgHomUnderlyingSpaceInfinity_vertex (M : RightModule R PUnit.{1}) :
    (dgHomUnderlyingSpaceInfinity R D).app (Opposite.op ⦋0⦌)
      (ULift.up (Simplex.vertex ((dgUniverseLiftUp R (RightModule R PUnit.{1})).obj M))) =
    (representablePresheafInfinity
      (Simplex.vertex ((dgUniverseLiftUp R (RightModule R PUnit.{1})).obj M) :
        (dgHomModuleNerve R D) _⦋0⦌)).app (Opposite.op ⦋0⦌)
      (ULift.up (SSet.opObjEquiv.symm (dgHomModuleUnitVertex R D))) := by
  dsimp only [dgHomUnderlyingSpaceInfinity, NatTrans.comp_app, types_comp_apply]
  rw [dgHomSpace_lift_app]
  change (homInfinityJointEvaluation (dgHomModuleNerve R D)).app (Opposite.op ⦋0⦌)
    (PinchedHom.constant (ULift.up (SSet.opObjEquiv.symm (dgHomModuleUnitVertex R D)) :
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
        (dgHomModuleNerve R D).op) _⦋0⦌) 0,
      ULift.up (Simplex.vertex ((dgUniverseLiftUp R (RightModule R PUnit.{1})).obj M))) = _
  rw [pinchedConstant_zero]
  exact dgHomSpace_joint_vertex (C := dgHomModuleNerve R D) _ _

/-- 同じ全空間値は、元の評価複体の実 pinched 模型と同値。 -/
def dgHomUnderlyingSpaceValueEquivalence (M : RightModule R PUnit.{1}) :
    QCatEquivalence (spaceInfinityObject ((dgHomUnderlyingSpaceInfinity R D).app
      (Opposite.op ⦋0⦌)
      (ULift.up (Simplex.vertex ((dgUniverseLiftUp R (RightModule R PUnit.{1})).obj M))))).obj
      (complexPinchedSpace.{u, max (u + 1) v} (M.obj (Opposite.op PUnit.unit))) := by
  rw [dgHomUnderlyingSpaceInfinity_vertex]
  exact (representablePresheafValueEquivalence
    (dgHomModuleUnitVertex R D)
    (Simplex.vertex ((dgUniverseLiftUp R (RightModule R PUnit.{1})).obj M))).trans
      (qCatEquivalenceOfIso (dgHomModuleUnderlyingPinchedIso R D M))
end SerrePositivity.InfinityCategories
