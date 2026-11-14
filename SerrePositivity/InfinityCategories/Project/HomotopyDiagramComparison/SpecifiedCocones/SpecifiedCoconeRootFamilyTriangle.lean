module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceEdgeFamilyTriangle
public import
  SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SpecifiedCoconeLeftRootNativeCylinder
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SpecifiedCoconeRootNativeCylinder

/-!
概要：左右の元の共通脚の全 Hom 族を、既存の native 比較円柱を二面に保って照合する。
方針：共通脚と終点係数の厳密な一致から、終点固定の全辺族の三角形を構成する。
規約：左右の比較円柱の raw な射と元の共通脚を保持する。
使われ方：指定輸送路の作用と左右の Hom 比較の合成を照合する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p)) (y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)
local notation "e" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeNativeRootEdge hp p c hc dB dC
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootBaseEdgeFiberFamily hp p c hc dB dC y
local notation "R" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootBaseEdgeFiberFamily hp p c hc dB dC y
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (f ≫ (i ≫ p))
local notation "T" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC)) y
local notation "P" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber e (stdSimplex.δ (1 : Fin 2))
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeNativeRootEdge_source hp p c hc dB dC) y ≫
    Iso.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q c y)

/-- 左右の元の全辺族の終点係数は、正規化前にも厳密に一致する。 -/
lemma specifiedCoconeRootFamilies_target :
    L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y =
      R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y := by
  have h := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootBaseEdgeFiberFamily_target hp p c hc dB dC y).trans
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootBaseEdgeFiberFamily_target hp p c hc dB dC y).symm
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber_eq, ← Category.assoc] at h
  exact (cancel_mono _).mp h

local notation "hLR" => specifiedCoconeRootFamilies_target hp p c hc dB dC y

/-- 二つの元の切断比較を二面に保つ、同じ native 共通脚上の全 Hom の三角形。 -/
def specifiedCoconeRootFamilyTriangle := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFamilyTriangle e y L R hLR

/-- 第一辺は、左三角形と右四面体の全辺族を結ぶ実際の円柱。 -/
def specifiedCoconeRootFamilyComparison : SSet.Homotopy L R :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFamilyComparison e y L R hLR

/-- 全辺族の比較は、終点係数を全時刻で固定する。 -/
lemma specifiedCoconeRootFamilyComparison_target :
    (specifiedCoconeRootFamilyComparison hp p c hc dB dC y).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y =
      CartesianMonoidalCategory.fst T Δ[1] ≫ L ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFamilyComparison_target e y L R hLR

/-- 全辺族の同じ第一辺を、左右の既存の中間 Hom の始点射影として表示する。 -/
def specifiedCoconeRootInitialProjectionComparison : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftInitialHomFamily hp p c hc dB dC y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q c y).hom)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedInitialHomFamily hp p c hc dB dC y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q c y).hom) where
  h := (specifiedCoconeRootFamilyComparison hp p c hc dB dC y).h ≫ P
  h₀ := by
    refine ((Category.assoc _ _ _).symm.trans (congrArg (fun k ↦ k ≫ P)
      (specifiedCoconeRootFamilyComparison hp p c hc dB dC y).h₀)).trans ?_
    exact ((Category.assoc _ _ _).symm.trans
      (congrArg (fun k ↦ k ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q c y).hom)
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootBaseEdgeFiberFamily_source hp p c hc dB dC y))).trans
      (Category.assoc _ _ _)
  h₁ := by
    refine ((Category.assoc _ _ _).symm.trans (congrArg (fun k ↦ k ≫ P)
      (specifiedCoconeRootFamilyComparison hp p c hc dB dC y).h₁)).trans ?_
    exact ((Category.assoc _ _ _).symm.trans
      (congrArg (fun k ↦ k ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q c y).hom)
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootBaseEdgeFiberFamily_source hp p c hc dB dC y))).trans
      (Category.assoc _ _ _)
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- 同じ三角形の第二面は、選択済みの右 native 比較円柱の射そのもの。 -/
lemma specifiedCoconeRootFamilyTriangle_second_projection :
    (T ◁ stdSimplex.δ (0 : Fin 3)) ≫
        ((specifiedCoconeRootFamilyTriangle hp p c hc dB dC y).family ≫ P) =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootNativeCylinder hp p c hc dB dC y).h := by
  refine ((Category.assoc _ _ _).symm.trans (congrArg (fun k ↦ k ≫ P)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFamilyTriangle_second e y L R hLR))).trans ?_
  exact (Category.assoc _ _ _).symm.trans
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootNativeCylinder_projection hp p c hc dB dC y).symm

/-- 同じ三角形の対角面は、選択済みの左 native 比較円柱の射そのもの。 -/
lemma specifiedCoconeRootFamilyTriangle_diagonal_projection :
    (T ◁ stdSimplex.δ (1 : Fin 3)) ≫
        ((specifiedCoconeRootFamilyTriangle hp p c hc dB dC y).family ≫ P) =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootNativeCylinder hp p c hc dB dC y).h := by
  refine ((Category.assoc _ _ _).symm.trans (congrArg (fun k ↦ k ≫ P)
    (specifiedCoconeRootFamilyTriangle hp p c hc dB dC y).diagonal)).trans ?_
  exact (Category.assoc _ _ _).symm.trans
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootNativeCylinder_projection hp p c hc dB dC y).symm

/-- 左右の native 比較の類は、実際の全辺族の第一辺で結ばれる。 -/
lemma specifiedCoconeRootFamilyTriangle_homMk_comp :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (specifiedCoconeRootInitialProjectionComparison hp p c hc dB dC y)) ≫
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootNativeCylinder hp p c hc dB dC y)) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootNativeCylinder hp p c hc dB dC y)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyTriangle_homMk_comp _ _ _
    ((specifiedCoconeRootFamilyTriangle hp p c hc dB dC y).family ≫ P)
  · exact (Category.assoc _ _ _).symm
  · exact specifiedCoconeRootFamilyTriangle_second_projection hp p c hc dB dC y
  · exact specifiedCoconeRootFamilyTriangle_diagonal_projection hp p c hc dB dC y

/-- 同じ終点族を保つ指定経路の全辺族が得られれば、その類はこの第一辺に一意に一致する。 -/
lemma specifiedCoconeRootFamilyComparison_homMk_unique (K : SSet.Homotopy L R)
    (hK : K.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y =
      CartesianMonoidalCategory.fst T Δ[1] ≫ L ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy K) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (specifiedCoconeRootFamilyComparison hp p c hc dB dC y)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFamilyComparison_homMk_unique e y L R hLR K hK

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
