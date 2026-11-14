module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientRoofLocallyConstant
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierOverTerminal
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.RoofTerminalFiberCofinality

/-! # 固定商 Hom と実商屋根の全空間の比較

概要：固定商 Hom は、実恒等分母の fiber を通して実商屋根の全空間へ right cofinal に写る。
方針：実恒等分母の終対象性と商屋根射影の左ファイブレーション性を接続する。
規約：全空間との圏同値は主張しない。使われ方：実屋根の弱ホモトピー比較の商側。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 固定商 Hom を、実恒等分母の fiber として商屋根の全空間へ含める。 -/
def dgQuotientFixedHomRoofMap (P : Set D) (x y : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (DGQuotient.QuotientObject D P)
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ⟶
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondence A D P x y :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceFiberIso A D P x y
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverIdentityVertex A D P x)).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceProjection A D P x y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverIdentityVertex A D P x)

/-- 固定商 Hom の実商屋根全空間への包含は right cofinal。 -/
theorem dgQuotientFixedHomRoofMap_isRightCofinal (P : Set D)
    (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P) (x y : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (dgQuotientFixedHomRoofMap A D P x y) := by
  have := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceProjection_leftFibration A D P hP x y
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.roofLeftFibration_terminalFiber_isRightCofinal
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceProjection A D P x y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverIdentityVertex A D P x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverIdentityVertex_isTerminal A D P x)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_rightAnodyne _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions.of_isIso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceFiberIso A D P x y
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverIdentityVertex A D P x)).inv)).comp h

/-- 固定商 Hom は実商屋根の全空間と弱ホモトピー同値。 -/
lemma dgQuotientFixedHomRoofMap_isWeakHomotopyEquivalence (P : Set D)
    (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P) (x y : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (dgQuotientFixedHomRoofMap A D P x y) :=
  (dgQuotientFixedHomRoofMap_isRightCofinal A D P hP x y).isWeakHomotopyEquivalence

/-- 元の固定 Hom を、同じ実恒等分母の fiber として元の屋根へ含める。 -/
def dgOriginalFixedHomRoofMap (P : Set D) (x y : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x y :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceFiberIso A D P x y (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverIdentityVertex A D P x)).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceProjection A D P x y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverIdentityVertex A D P x)

/-- 元の固定 Hom・固定商 Hom の屋根への包含は、商比較と厳密に可換。 -/
lemma dgFixedHomRoofMap_comparison (P : Set D) (x y : D) :
    dgOriginalFixedHomRoofMap A D P x y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((DGQuotient.inclusion A D P).map x y) ≫
        dgQuotientFixedHomRoofMap A D P x y := by
  let σ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverIdentityVertex A D P x
  have h : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceFiberIso A D P x y σ).inv ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceFiberMap A D P x y σ =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((DGQuotient.inclusion A D P).map x y) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceFiberIso A D P x y σ).inv := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceFiberIso A D P x y σ).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceFiberMap_conjugate A D P x y σ
  dsimp only [dgOriginalFixedHomRoofMap, dgQuotientFixedHomRoofMap]
  rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceFiberMap_ι, ← Category.assoc, h, Category.assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
