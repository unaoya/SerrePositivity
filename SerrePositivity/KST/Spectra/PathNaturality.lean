module

public import SerrePositivity.KST.Spectra.LoopPathFiber
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FibrationNaturalityAt
public import SerrePositivity.KST.Spectra.PointedHomotopy

/-!
概要：path の終点評価と loop の fiber 表示の自然性。
方針：閉構造の前合成・後合成の可換性と fiber 包含による一意性を使う。
規約：定数 path を指定基点にして移送する。
使われ方：Goerss–Jardine I §7、BF 1978 §2。loop の次数移動の自然性。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：点つき Hom の前合成と後合成は可換。
方針：前合成を閉構造の pre と同定する。
規約：全て通常の点つき射。
使われ方：Goerss–Jardine I §7。path の評価の自然性。 -/
theorem PointedMapping.prePointed_post {A B E Z : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (p : E ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i E ≫ PointedObject.basedHomMap A p =
      PointedObject.basedHomMap B p ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z := by
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
  exact MonoidalClosed.pre_comm_ihom_map i p

/-- 概要：点つき射が path に誘導する射。
方針：区間からの点つき Hom の後合成を使う。
規約：定数 path を保存する。
使われ方：Goerss–Jardine I §7。path fibration の可換正方形。 -/
def basedPathMap {Y Z : PointedSimplicialSet.{u}} (p : Y ⟶ Z) :
    basedPathSpace Y ⟶ basedPathSpace Z := PointedObject.basedHomMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u} p

/-- 概要：path の終点評価は標的の点つき射に関して自然。
方針：端点の前合成の自然性と単位からの内部 Hom の自然な同型を使う。
規約：点つき射の厳密な可換式。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。長完全列の自然性。 -/
@[reassoc]
theorem pathEndpoint_natural {Y Z : PointedSimplicialSet.{u}} (p : Y ⟶ Z) :
    basedPathMap p ≫ pathEndpoint Z = pathEndpoint Y ≫ p := by
  unfold basedPathMap pathEndpoint
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
  change (ihom _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}).map p ≫ (MonoidalClosed.pre _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}).app Z ≫
      (MonoidalClosed.unitNatIso (C := PointedSimplicialSet.{u})).inv.app Z =
    ((MonoidalClosed.pre _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}).app Y ≫
      (MonoidalClosed.unitNatIso (C := PointedSimplicialSet.{u})).inv.app Y) ≫ p
  rw [← Category.assoc, ← MonoidalClosed.pre_comm_ihom_map, Category.assoc]
  rw [(MonoidalClosed.unitNatIso (C := PointedSimplicialSet.{u})).inv.naturality p]
  rfl

/-- 概要：loop の円の表示の同型は標的に関して自然。
方針：円の同型による pre と標的での後合成の可換性を使う。
規約：点つき同型の順方向の式。
使われ方：Goerss–Jardine I §7。loop の fiber 表示の自然性。 -/
theorem loopToEndpointHomIso_natural {Y Z : PointedSimplicialSet.{u}} (p : Y ⟶ Z) :
    PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p ≫ (loopToEndpointHomIso Z).hom =
      (loopToEndpointHomIso Y).hom ≫ PointedObject.basedHomMap endpointCircle.{u} p := by
  change (ihom PointedSimplicialSet.circle.{u}).map p ≫
      (MonoidalClosed.pre endpointCircleIso.{u}.hom).app Z =
    (MonoidalClosed.pre endpointCircleIso.{u}.hom).app Y ≫ (ihom endpointCircle.{u}).map p
  exact (MonoidalClosed.pre_comm_ihom_map endpointCircleIso.hom p).symm

/-- 概要：loop を全 path に含める射は標的に関して自然。
方針：円の表示の同型と cofiber 射による前合成の自然性を合成する。
規約：点つき射で述べる。
使われ方：Goerss–Jardine I §7。fiber の包含後の自然性の検査。 -/
theorem loopToPath_natural {Y Z : PointedSimplicialSet.{u}} (p : Y ⟶ Z) :
    PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p ≫
        ((loopToEndpointHomIso Z).hom ≫
          _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (pointedCofiberProjection _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}) Z) =
      ((loopToEndpointHomIso Y).hom ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (pointedCofiberProjection _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}) Y) ≫
          basedPathMap p := by
  rw [← Category.assoc, loopToEndpointHomIso_natural, Category.assoc,
    ← PointedMapping.prePointed_post, ← Category.assoc]
  rfl

/-- 概要：path の終点の指定基点上の fiber 間の射。
方針：終点評価の自然な可換正方形に指定基点の fiberMapAt を使う。
規約：両側とも定数 path の fiberPoint と一致する基点を使う。
使われ方：Goerss–Jardine I §7。連結写像と loop の同型の自然性。 -/
def pathFiberMap {Y Z : PointedSimplicialSet.{u}} (p : Y ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber (pathEndpoint Y).right ((pathEndpoint Y).right.app _ (basedPathSpace Y).basepoint) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber (pathEndpoint Z).right ((pathEndpoint Z).right.app _ (basedPathSpace Z).basepoint) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.fiberMapAt (pathEndpoint Y).right (pathEndpoint Z).right
    (basedPathMap p).right p.right (congrArg Under.Hom.right (pathEndpoint_natural p)).symm
    (basedPathSpace Y).basepoint (basedPathSpace Z).basepoint
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (basedPathMap p))

/-- 概要：path の fiber 間の射は全 path への包含と可換。
方針：指定基点の fiberMapAt の包含の式を使う。
規約：全空間の射は後合成による basedPathMap。
使われ方：Goerss–Jardine I §7。loop の同型の自然性。 -/
@[reassoc (attr := simp)]
theorem pathFiberMap_ι {Y Z : PointedSimplicialSet.{u}} (p : Y ⟶ Z) :
    pathFiberMap p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι (pathEndpoint Z).right
      ((pathEndpoint Z).right.app _ (basedPathSpace Z).basepoint) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι (pathEndpoint Y).right
          ((pathEndpoint Y).right.app _ (basedPathSpace Y).basepoint) ≫ (basedPathMap p).right :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.fiberMapAt_ι _ _ _ _ _ _ _ _

/-- 概要：path の fiber 間の射は定数 path の fiberPoint を保つ。
方針：指定基点の fiberMapAt の基点の式を使う。
規約：両基点は標的ごとの定数 path から定まる。
使われ方：Goerss–Jardine I §7。loop のホモトピー群の自然性。 -/
@[simp]
theorem pathFiberMap_point {Y Z : PointedSimplicialSet.{u}} (p : Y ⟶ Z) :
    (pathFiberMap p).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint (pathEndpoint Y).right (basedPathSpace Y).basepoint) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint (pathEndpoint Z).right (basedPathSpace Z).basepoint :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.fiberMapAt_point _ _ _ _ _ _ _ _

/-- 概要：path の底の指定基点の像を表す等式。
方針：終点評価の自然性を頂点で評価して指定基点へ移す。
規約：π_* の基点移送のため、通常の標的の基点とは区別する。
使われ方：Goerss–Jardine I §7。path の連結写像の自然性。 -/
theorem pathFiberMap_base {Y Z : PointedSimplicialSet.{u}} (p : Y ⟶ Z) :
    p.right.app _ ((pathEndpoint Y).right.app _ (basedPathSpace Y).basepoint) =
      (pathEndpoint Z).right.app _ (basedPathSpace Z).basepoint :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.base_eqAt (pathEndpoint Y).right (pathEndpoint Z).right
    (basedPathMap p).right p.right (congrArg Under.Hom.right (pathEndpoint_natural p)).symm
    (basedPathSpace Y).basepoint (basedPathSpace Z).basepoint
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (basedPathMap p))

/-- 概要：path の連結写像は標的の点つき射に関して全次数で自然。
方針：終点評価の可換正方形に指定基点の自然性を適用する。
規約：零次数の fiber の類も含む。
使われ方：Goerss–Jardine I §7。loop の次数移動の自然性。 -/
theorem pathConnecting_natural {Y Z : PointedSimplicialSet.{u}}
    [KanComplex Y.right] [KanComplex Z.right] (p : Y ⟶ Z) (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right n
      ((pathEndpoint Y).right.app _ (basedPathSpace Y).basepoint)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (pathFiberMap p) (pathFiberMap_point p)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting (pathEndpoint Y).right (basedPathSpace Y).basepoint n a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting (pathEndpoint Z).right (basedPathSpace Z).basepoint n
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map p.right (pathFiberMap_base p) a) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.connecting_natural_at (pathEndpoint Y).right (pathEndpoint Z).right
    (basedPathMap p).right p.right (congrArg Under.Hom.right (pathEndpoint_natural p)).symm
    (basedPathSpace Y).basepoint (basedPathSpace Z).basepoint
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (basedPathMap p)) n a

/-- 概要：loop と定数 path 上の fiber の同型は標的に関して自然。
方針：fiber の全空間への包含で比較し、点つき loop の包含の自然性を使う。
規約：実際の単体集合の射の等式であり導来比較ではない。
使われ方：Goerss–Jardine I §7、BF 1978 §2。loop の次数移動の自然性。 -/
theorem loopBasedPathFiberIso_natural {Y Z : PointedSimplicialSet.{u}} (p : Y ⟶ Z) :
    (loopBasedPathFiberIso Y).hom ≫ pathFiberMap p =
      (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p).right ≫
        (loopBasedPathFiberIso Z).hom := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext (pathEndpoint Z).right _
  rw [Category.assoc, pathFiberMap_ι, ← Category.assoc, loopBasedPathFiberIso_hom_ι,
    Category.assoc, loopBasedPathFiberIso_hom_ι]
  exact (congrArg Under.Hom.right (loopToPath_natural p)).symm

end

end SerrePositivity.KST.Spectra
