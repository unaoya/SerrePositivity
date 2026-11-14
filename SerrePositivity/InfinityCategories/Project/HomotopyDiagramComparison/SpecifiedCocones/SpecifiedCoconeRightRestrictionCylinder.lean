module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SpecifiedCoconeRootedHomCylinder
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialEvaluationHomotopyTriangle
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.PartialColimitHomEnd

/-!
概要：共通 end の右制限の円柱と元の指定四面体の円柱を、同じ全 Hom 上で比較する。
方針：右制限の評価固定円柱に元の全 Hom 族を前合成し、両円柱を保つ三角形を充填する。
規約：元の HR・四面体・全 Hom パラメータと同じ終点評価を同時に保持する。
使われ方：共通 path end の右側係数の高次照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p))
  (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone dC) (y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (f ≫ (i ≫ p))
local notation "V" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeCommonHomFamily hp p c hc dB dC y
local notation "DR" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentRestrictionCylinderData c hc g (j ≫ p)
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC hC y

/-- 元の指定余錐の全 Hom 族を右側へ制限した、同じ実際の族。 -/
def specifiedCoconeRightHomRestriction :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (j ≫ p) y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC) y ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p j y
local notation "U" => specifiedCoconeRightHomRestriction hp p c hc dB dC y

/-- HR の元の中間持ち上げに、同じ全 Hom の右制限族を前合成する。 -/
def specifiedCoconeRightRestrictionInitialHomFamily :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialTotal q c y :=
  U ≫ (DR).lift

/-- HR の同じ評価固定円柱を、元の指定余錐の全 Hom パラメータで読む。 -/
def specifiedCoconeRightRestrictionInitialHomCylinder : SSet.Homotopy
    (V ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialSection q c hc y)
    (specifiedCoconeRightRestrictionInitialHomFamily hp p c hc dB dC hC y) := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (DR).homotopy U
  exact
    { h := H.h
      h₀ := by
        change SSet.ι₀ ≫ H.h = V ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialSection q c hc y
        simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionEdgeFamily_vertexFiberLift, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber,
          specifiedCoconeRightHomRestriction, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeCommonHomFamily, Category.assoc]
          using H.h₀
      h₁ := by
        change SSet.ι₁ ≫ H.h = specifiedCoconeRightRestrictionInitialHomFamily hp p c hc dB dC hC y
        exact H.h₁
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro z
        exact False.elim z.1.property }

/-- 全 Hom を前合成しても、同じ共通部分の族を全時刻で評価する。 -/
lemma specifiedCoconeRightRestrictionInitialHomCylinder_evaluation :
    (specifiedCoconeRightRestrictionInitialHomCylinder hp p c hc dB dC hC y).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation q c y = fst _ (Δ[1] : SSet.{u + 1}) ≫ V := by
  change ((U ▷ (Δ[1] : SSet.{u + 1})) ≫ (DR).homotopy.h) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation q c y = _
  let r := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber (j ≫ p) g (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) y
  have hV : U ≫ r = V := Category.assoc _ _ _
  calc
    _ = (U ▷ (Δ[1] : SSet.{u + 1})) ≫
        ((DR).homotopy.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation q c y) := Category.assoc _ _ _
    _ = (U ▷ (Δ[1] : SSet.{u + 1})) ≫ (fst _ Δ[1] ≫ r) :=
      congrArg (fun k ↦ (U ▷ (Δ[1] : SSet.{u + 1})) ≫ k)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentRestrictionCylinderData_evaluation c hc g (j ≫ p)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC hC y)
    _ = ((U ▷ (Δ[1] : SSet.{u + 1})) ≫ fst _ Δ[1]) ≫ r := (Category.assoc _ _ _).symm
    _ = (fst _ Δ[1] ≫ U) ≫ r := congrArg (fun k ↦ k ≫ r) (whiskerRight_fst U Δ[1])
    _ = fst _ Δ[1] ≫ V := (Category.assoc _ _ _).trans (congrArg (fun k ↦ fst _ Δ[1] ≫ k) hV)

/-- HR と元の四面体の比較円柱の両方を二辺として保つ、実際の同じ評価上の三角形。 -/
def specifiedCoconeRightRestrictionRootedTriangle : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialEvaluationHomotopyTriangle q c y V
    (specifiedCoconeRightRestrictionInitialHomCylinder hp p c hc dB dC hC y)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedHomCylinder hp p c hc dB dC y).homotopy :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialEvaluationHomotopyTriangle q c y V _ _ hc
    (specifiedCoconeRightRestrictionInitialHomCylinder_evaluation hp p c hc dB dC hC y)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedHomCylinder hp p c hc dB dC y).evaluation

/-- 同じ三角形の第三辺による、右制限の中間族と元の四面体全体の中間族の比較。 -/
def specifiedCoconeRightRestrictionRootedHomotopy : SSet.Homotopy
    (specifiedCoconeRightRestrictionInitialHomFamily hp p c hc dB dC hC y)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedInitialHomFamily hp p c hc dB dC y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialEvaluationHomotopyTriangleThird q c y V _ _
    (specifiedCoconeRightRestrictionRootedTriangle hp p c hc dB dC hC y)

/-- 第三辺も元の全 Hom 族の共通部分への制限を全時刻で保つ。 -/
lemma specifiedCoconeRightRestrictionRootedHomotopy_evaluation :
    (specifiedCoconeRightRestrictionRootedHomotopy hp p c hc dB dC hC y).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation q c y = fst _ (Δ[1] : SSet.{u + 1}) ≫ V :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialEvaluationHomotopyTriangleThird_evaluation _ _ _ _ _ _ _

/-- 三角形の第一辺の射影は、共通 end が使う元の HR に全 Hom を前合成した同じ円柱。 -/
lemma specifiedCoconeRightRestrictionRootedTriangle_first_projection :
    (_ ◁ stdSimplex.δ (2 : Fin 3)) ≫
        ((specifiedCoconeRightRestrictionRootedTriangle hp p c hc dB dC hC y).family ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q c y).hom) =
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitHomEndRightCylinder hp p y c hc dC hC) U).h := by
  calc
    _ = ((_ ◁ stdSimplex.δ (2 : Fin 3)) ≫
        (specifiedCoconeRightRestrictionRootedTriangle hp p c hc dB dC hC y).family) ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q c y).hom) :=
      (Category.assoc _ _ _).symm
    _ = (specifiedCoconeRightRestrictionInitialHomCylinder hp p c hc dB dC hC y).h ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q c y).hom) :=
      congrArg (fun k ↦ k ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q c y).hom))
          (specifiedCoconeRightRestrictionRootedTriangle hp p c hc dB dC hC y).first
    _ = _ := Category.assoc _ _ _

/-- 三角形の対角辺の射影も、元の指定四面体の全 Hom 比較の円柱そのもの。 -/
lemma specifiedCoconeRightRestrictionRootedTriangle_diagonal_projection :
    (_ ◁ stdSimplex.δ (1 : Fin 3)) ≫
        ((specifiedCoconeRightRestrictionRootedTriangle hp p c hc dB dC hC y).family ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q c y).hom) =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedHomCylinderComparison hp p c hc dB dC y).h := by
  calc
    _ = ((_ ◁ stdSimplex.δ (1 : Fin 3)) ≫
        (specifiedCoconeRightRestrictionRootedTriangle hp p c hc dB dC hC y).family) ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q c y).hom) :=
      (Category.assoc _ _ _).symm
    _ = (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedHomCylinder hp p c hc dB dC y).homotopy.h ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q c y).hom) :=
      congrArg (fun k ↦ k ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q c y).hom))
          (specifiedCoconeRightRestrictionRootedTriangle hp p c hc dB dC hC y).diagonal
    _ = _ := rfl

/-- 同じ三角形の第三辺を左 Hom へ射影した、元の両中間族の全 Hom 比較。 -/
def specifiedCoconeRightRestrictionRootedHomComparison : SSet.Homotopy
    (specifiedCoconeRightRestrictionInitialHomFamily hp p c hc dB dC hC y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q c y).hom)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedInitialHomFamily hp p c hc dB dC y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q c y).hom) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (specifiedCoconeRightRestrictionRootedHomotopy hp p c hc dB dC hC y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q c y).hom)

/-- 第三辺の比較も、同じ中間三角形の辺の射影を保持する。 -/
lemma specifiedCoconeRightRestrictionRootedHomComparison_projection :
    (specifiedCoconeRightRestrictionRootedHomComparison hp p c hc dB dC hC y).h =
      (specifiedCoconeRightRestrictionRootedHomotopy hp p c hc dB dC hC y).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q c y).hom := rfl

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
