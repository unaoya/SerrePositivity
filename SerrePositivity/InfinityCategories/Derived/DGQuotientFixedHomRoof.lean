module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientRoofLocallyConstant
public import SerrePositivity.InfinityCategories.Derived.DGVerdierOverTerminal
public import SerrePositivity.InfinityCategories.Derived.RoofTerminalFiberCofinality

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 固定商 Hom を、実恒等分母の fiber として商屋根の全空間へ含める。 -/
def dgQuotientFixedHomRoofMap (P : Set D) (x y : D) :
    DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
      ((DGQuotient.inclusion A D P).obj x) ((DGQuotient.inclusion A D P).obj y) ⟶
        dgQuotientRoofCorrespondence A D P x y :=
  (dgQuotientRoofCorrespondenceFiberIso A D P x y
    (dgVerdierOverIdentityVertex A D P x)).inv ≫
      vertexFiberι (dgQuotientRoofCorrespondenceProjection A D P x y)
        (dgVerdierOverIdentityVertex A D P x)

/-- 固定商 Hom の実商屋根全空間への包含は right cofinal。 -/
theorem dgQuotientFixedHomRoofMap_isRightCofinal (P : Set D)
    (hP : DGQuotient.localKFlat A D P) (x y : D) :
    IsRightCofinal (dgQuotientFixedHomRoofMap A D P x y) := by
  have := dgQuotientRoofCorrespondenceProjection_leftFibration A D P hP x y
  have h := roofLeftFibration_terminalFiber_isRightCofinal
    (dgQuotientRoofCorrespondenceProjection A D P x y)
    (dgVerdierOverIdentityVertex A D P x) (dgVerdierOverIdentityVertex_isTerminal A D P x)
  exact (isRightCofinal_of_rightAnodyne _ (rightAnodyneExtensions.of_isIso
    (dgQuotientRoofCorrespondenceFiberIso A D P x y
      (dgVerdierOverIdentityVertex A D P x)).inv)).comp h

/-- 固定商 Hom は実商屋根の全空間と弱ホモトピー同値。 -/
lemma dgQuotientFixedHomRoofMap_isWeakHomotopyEquivalence (P : Set D)
    (hP : DGQuotient.localKFlat A D P) (x y : D) :
    IsWeakHomotopyEquivalence (dgQuotientFixedHomRoofMap A D P x y) :=
  (dgQuotientFixedHomRoofMap_isRightCofinal A D P hP x y).isWeakHomotopyEquivalence

/-- 元の固定 Hom を、同じ実恒等分母の fiber として元の屋根へ含める。 -/
def dgOriginalFixedHomRoofMap (P : Set D) (x y : D) :
    DGNerve.pinchedHom A D x y ⟶ dgRoofCorrespondence A D P x y :=
  (dgRoofCorrespondenceFiberIso A D P x y (dgVerdierOverIdentityVertex A D P x)).inv ≫
    vertexFiberι (dgRoofCorrespondenceProjection A D P x y)
      (dgVerdierOverIdentityVertex A D P x)

/-- 元の固定 Hom・固定商 Hom の屋根への包含は、商比較と厳密に可換。 -/
lemma dgFixedHomRoofMap_comparison (P : Set D) (x y : D) :
    dgOriginalFixedHomRoofMap A D P x y ≫ dgRoofCorrespondenceMap A D P x y =
      pinchedHomChainMap ((DGQuotient.inclusion A D P).map x y) ≫
        dgQuotientFixedHomRoofMap A D P x y := by
  let σ := dgVerdierOverIdentityVertex A D P x
  have h : (dgRoofCorrespondenceFiberIso A D P x y σ).inv ≫
      dgRoofCorrespondenceFiberMap A D P x y σ =
      pinchedHomChainMap ((DGQuotient.inclusion A D P).map x y) ≫
        (dgQuotientRoofCorrespondenceFiberIso A D P x y σ).inv := by
    apply (cancel_mono (dgQuotientRoofCorrespondenceFiberIso A D P x y σ).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact dgRoofCorrespondenceFiberMap_conjugate A D P x y σ
  dsimp only [dgOriginalFixedHomRoofMap, dgQuotientFixedHomRoofMap]
  rw [Category.assoc, ← dgRoofCorrespondenceFiberMap_ι, ← Category.assoc, h, Category.assoc]

end SerrePositivity.InfinityCategories
