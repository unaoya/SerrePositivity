module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CylinderSquareRecoveredEndpoints

/-!
概要：円柱の中間模型から四角形への順比較は両端の fiber 写像を保つ。
方針：包含後の始点と終点を比較し、fiber の一意性で戻す。
規約：両端の同値を類まで弱めず厳密に保つ。
使われ方：同値な両端を持つ部分空間への順比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：fiber 値の関手の族は包含後の射で一意に決まる。
方針：uncurry と fiber の包含の一意性を使う。
規約：任意のパラメーターと係数で成立する。
使われ方：両端の fiber 写像の厳密な比較。 -/
lemma functorVertexFiber_hom_ext {A L E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    {F G : L ⟶ (ihom A).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b)}
    (h : F ≫ (ihom A).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) = G ≫ (ihom A).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b)) : F = G := by
  apply uncurry_injective
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
  simpa only [uncurry_natural_right] using congrArg uncurry h

/-- 概要：貼った全空間の族の始点は指定した始点 fiber の族。
方針：prism の始点への制限と貼り合わせの回収式を使う。
規約：包含後の射の厳密な等式。
使われ方：順比較の始点条件。 -/
lemma pointedCylinderPointedMap_source_ι {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPointedMap f s t ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderSquareSourceInclusion f)).app _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismSource f s t ≫ (ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection s) := by
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_natural_right]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderSquareSourceInclusion f ▷ _) ≫ uncurry (curry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderFamily f s t)) = _
  rw [uncurry_curry]
  have h : (pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) f ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismSpace f s t) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderFamily f s t = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismEvaluation f s t :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.parametrizedCylinderDesc_inl _ _ _ _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderSquareSourceInclusion, comp_whiskerRight, Category.assoc, h]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismEvaluation_zero f s t

/-- 概要：順比較で回収した始点は元の始点同値の族。
方針：包含後の始点評価で比較する。
規約：fiber 値の写像自体の等式。
使われ方：始点同値の部分空間への持ち上げ。 -/
lemma pointedCylinderFixedSquareMap_source {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedCylinderFixedSquareMap f s t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareSource f s t =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismSource f s t := by
  apply functorVertexFiber_hom_ext _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection s
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareSource_ι, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedCylinderFixedSquareMap_pointed]
  exact pointedCylinderPointedMap_source_ι f s t

/-- 概要：順比較で回収した終点は元の終点同値の族。
方針：包含後の終点評価で比較する。
規約：fiber 値の写像自体の等式。
使われ方：終点同値の部分空間への持ち上げ。 -/
lemma pointedCylinderFixedSquareMap_target {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedCylinderFixedSquareMap f s t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareTarget f s t =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismTarget f s t := by
  apply functorVertexFiber_hom_ext _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection t
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareTarget_ι, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedCylinderFixedSquareMap_pointed]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPointedMap_inr f s t

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
