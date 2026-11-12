module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleUnitPinchedModel
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleHomSpaceInfinity
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v)
/-- 全 dg R 加群から R を始域とする写像空間への、全単体を保持する ∞ 関手。 -/
def dgHomUnderlyingSpaceInfinity :
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleNerve R D) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{max (u + 1) v} :=
  CartesianMonoidalCategory.lift
    (SSet.const (ULift.up (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnitVertex R D))))
    (𝟙 _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homInfinityJointEvaluation (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleNerve R D)
/-- 同じ空間値関手の頂点値は、同じ Hom 関手の共同評価。 -/
lemma dgHomUnderlyingSpaceInfinity_vertex (M : _root_.SerrePositivity.DifferentialGraded.RightModule R PUnit.{1}) :
    (dgHomUnderlyingSpaceInfinity R D).app (Opposite.op ⦋0⦌)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R PUnit.{1})).obj M))) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R PUnit.{1})).obj M) :
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleNerve R D) _⦋0⦌)).app (Opposite.op ⦋0⦌)
      (ULift.up (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnitVertex R D))) := by
  dsimp only [dgHomUnderlyingSpaceInfinity, NatTrans.comp_app, types_comp_apply]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomSpace_lift_app]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homInfinityJointEvaluation (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleNerve R D)).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (ULift.up (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnitVertex R D)) :
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleNerve R D).op) _⦋0⦌) 0,
      ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R PUnit.{1})).obj M))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomSpace_joint_vertex (C := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleNerve R D) _ _

/-- 同じ全空間値は、元の評価複体の実 pinched 模型と同値。 -/
def dgHomUnderlyingSpaceValueEquivalence (M : _root_.SerrePositivity.DifferentialGraded.RightModule R PUnit.{1}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject ((dgHomUnderlyingSpaceInfinity R D).app
      (Opposite.op ⦋0⦌)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R PUnit.{1})).obj M))))).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (M.obj (Opposite.op PUnit.unit))) := by
  rw [dgHomUnderlyingSpaceInfinity_vertex]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafValueEquivalence
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnitVertex R D)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R PUnit.{1})).obj M))).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnderlyingPinchedIso R D M))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
