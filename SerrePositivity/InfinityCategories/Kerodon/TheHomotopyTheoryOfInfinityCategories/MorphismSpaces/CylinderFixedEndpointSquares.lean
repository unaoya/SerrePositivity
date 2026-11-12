module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PointedCylinderSquare

/-!
概要：底の区間の両端を厳密に固定した円柱上の可換四角形の空間。
方針：区間写像空間を底の関手空間へ含めて可換四角形の引き戻しを取る。
規約：両端の同値条件を課す前の全四角形の空間。
使われ方：prism の中間模型との逆比較を定義する周囲の空間。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：両端固定の区間写像空間の全関手空間への包含。
方針：定義の頂点 fiber の包含。
規約：高次の底の族の両端を厳密に固定する。
使われ方：両端固定の可換四角形の底。 -/
def cylinderIntervalDiagramι (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace s t ⟶ (ihom (Δ[1] : SSet.{u + 1})).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((pre (boundary 1).ι).app _) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingBoundary s t))

/-- 概要：底の両端を s,t に固定した円柱上の実際の可換四角形の空間。
方針：pointed-space への後合成と底の区間による前合成を引き戻す。
規約：円柱の係数に充填性は要求しない。
使われ方：円柱の表現条件を課す前の比較対象。 -/
def cylinderFixedEndpointSquareSpace {K J : SSet.{u + 1}} (f : K ⟶ J)
    (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) : SSet.{u + 1} :=
  pullback ((ihom (pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) f)).map _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection)
    (cylinderIntervalDiagramι s t ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderIntervalProjection f)).app _)

/-- 概要：両端固定四角形の全空間の関手の族。
方針：引き戻しの第一射影。
規約：実際の円柱上の射を保持する。
使われ方：逆比較で prism と終点の族を取り出す。 -/
def cylinderFixedEndpointSquarePointed {K J : SSet.{u + 1}} (f : K ⟶ J)
    (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    cylinderFixedEndpointSquareSpace f s t ⟶
      (ihom (pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) f)).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u} := pullback.fst _ _

/-- 概要：両端固定四角形の底の区間の族。
方針：引き戻しの第二射影。
規約：底の両端は s,t に固定されている。
使われ方：逆比較の底のパラメーター。 -/
def cylinderFixedEndpointSquareInterval {K J : SSet.{u + 1}} (f : K ⟶ J)
    (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    cylinderFixedEndpointSquareSpace f s t ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace s t := pullback.snd _ _

/-- 概要：両端固定四角形の普遍評価は指定された底の区間族を覆う。
方針：引き戻し条件を uncurry する。
規約：全高次パラメーターでの厳密な可換性。
使われ方：端点の評価を普遍 pointed-space fiber に持ち上げる。 -/
lemma cylinderFixedEndpointSquare_base {K J : SSet.{u + 1}} (f : K ⟶ J)
    (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    uncurry (cylinderFixedEndpointSquarePointed f s t) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderIntervalProjection f ▷ cylinderFixedEndpointSquareSpace f s t) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (cylinderFixedEndpointSquareInterval f s t) := by
  have h := congrArg uncurry (pullback.condition (f :=
    (ihom (pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) f)).map _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection)
    (g := cylinderIntervalDiagramι s t ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderIntervalProjection f)).app _))
  change uncurry (cylinderFixedEndpointSquarePointed f s t ≫
      (ihom (pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) f)).map _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection) =
    uncurry ((cylinderFixedEndpointSquareInterval f s t ≫ cylinderIntervalDiagramι s t) ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderIntervalProjection f)).app _) at h
  rw [uncurry_natural_right, uncurry_pre_app] at h
  exact h

/-- 概要：円柱の prism 中間空間から両端固定の実際の四角形の空間への比較。
方針：貼った全空間の族と元の区間パラメーターを引き戻しへ写す。
規約：底の両端と全空間の射の両方を保持する。
使われ方：逆比較との往復を検証する順方向の射。 -/
def pointedCylinderFixedSquareMap {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismSpace f s t ⟶ cylinderFixedEndpointSquareSpace f s t :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPointedMap f s t) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderInterval f s t) (by
    have h : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderInterval f s t ≫ cylinderIntervalDiagramι s t =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderDiagram f s t := (curry_uncurry _).symm
    rw [← Category.assoc, h]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPointedMap_condition f s t)

/-- 概要：両端固定四角形への比較は貼った全空間の族を回収する。
方針：引き戻しの第一射影。
規約：射そのものの等式。
使われ方：逆比較での prism と終点の回収。 -/
lemma pointedCylinderFixedSquareMap_pointed {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    pointedCylinderFixedSquareMap f s t ≫ cylinderFixedEndpointSquarePointed f s t =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPointedMap f s t := pullback.lift_fst _ _ _

/-- 概要：両端固定四角形への比較は元の区間の族を回収する。
方針：引き戻しの第二射影。
規約：底の射の厳密な等式。
使われ方：逆比較での底のパラメーターの回収。 -/
lemma pointedCylinderFixedSquareMap_interval {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    pointedCylinderFixedSquareMap f s t ≫ cylinderFixedEndpointSquareInterval f s t =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderInterval f s t := pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
