module
public import SerrePositivity.KST.Fibration.VerdierOriginalCompositeNativeEdge
public import SerrePositivity.KST.Fibration.FixedRestrictionFunctorPrism
public import SerrePositivity.KST.Fibration.ZeroMiddleControlledTriangleInput
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TrianglePathInterval
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.SquareHomotopyCategory

/-!
概要：元の全長 Hom 比較を、直接端を固定する実 native Kan 四角形として保持する。
方針：同じ比較円柱を元の path 区間座標へ制限する。
規約：元の上下 path・比較辺を保持し、新たな比較を選ばない。
使われ方：K-6 c4 の有限入力点で指定する合成二単体の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 概要：元の上下全長 Hom の実比較四角形。
方針：同じ固定直接端円柱を path 区間同型で読む。
規約：第一座標が元の長 Hom、第二座標が比較時刻。
使われ方：有限入力点の指定上側長 Hom を合成端比較と接続する。 -/
def verdierOriginalNativeHomSquare (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ verdierOriginalNativeHomTarget d :=
  (β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫
    (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleNativePathIntervalIso.inv) ≫
      (verdierOriginalNativeHomComparison d j k).prism

/-- 概要：比較四角形の下辺は元の始端全長 Hom。
方針：同じ円柱の時刻零の回収を区間座標へ制限する。
規約：元の全 path を保持する。
使われ方：有限点の始端辺を指定する。 -/
theorem verdierOriginalNativeHomSquare_bottom (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ verdierOriginalNativeHomSquare d j k =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleNativePathIntervalIso.inv ≫ verdierOriginalNativeHomFamily d j := by
  have hshape : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ (β_ (Δ[1] : SSet.{u}) Δ[1]).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge, lift_braiding_hom]
    rfl
  rw [verdierOriginalNativeHomSquare, ← Category.assoc, ← Category.assoc, hshape,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc]
  exact congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleNativePathIntervalIso.inv ≫ f)
    (verdierOriginalNativeHomComparison d j k).prism_zero

/-- 概要：比較四角形の上辺は元の終端全長 Hom。
方針：同じ円柱の時刻一の回収を区間座標へ制限する。
規約：元の全 path を保持する。
使われ方：有限点の指定終端辺を回収する。 -/
theorem verdierOriginalNativeHomSquare_top (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ verdierOriginalNativeHomSquare d j k =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleNativePathIntervalIso.inv ≫ verdierOriginalNativeHomFamily d k := by
  have hshape : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ (β_ (Δ[1] : SSet.{u}) Δ[1]).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge, lift_braiding_hom]
    rfl
  rw [verdierOriginalNativeHomSquare, ← Category.assoc, ← Category.assoc, hshape,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc]
  exact congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleNativePathIntervalIso.inv ≫ f)
    (verdierOriginalNativeHomComparison d j k).prism_one

/-- 概要：比較四角形の右辺は同じ元の実合成端比較辺。
方針：区間終点の全 path 回収を同じ円柱成分へ代入する。
規約：実一単体を同型類へ弱めない。
使われ方：指定長 Hom と既存の合成端移送を接続する。 -/
theorem verdierOriginalNativeHomSquare_right (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ verdierOriginalNativeHomSquare d j k =
      SSet.yonedaEquiv.symm (verdierOriginalCompositeCoreEdgeData d j k).val.edge := by
  rw [verdierOriginalNativeHomSquare, ← Category.assoc, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge, lift_braiding_hom, lift_whiskerLeft,
    SSet.const_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleNativePathIntervalIso_inv_last]
  rw [← verdierOriginalNativeHomComparison_full_edge, coherentTriangleFullPath_eq_univ]
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge := by
    apply SSet.stdSimplex.ext
    intro a
    fin_cases a <;> rfl
  change (verdierOriginalNativeHomComparison d j k).prism.app (Opposite.op ⦋1⦌)
    (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _) =
      (verdierOriginalNativeHomComparison d j k).prism.app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge, _)
  rw [hi]
  rfl

/-- 概要：比較四角形の左辺は元の直接端の恒等辺の全区間族。
方針：元の固定直接端比較の全円柱回収を区間始点へ代入する。
規約：同じ実直接端を厳密保持する。
使われ方：有限入力点で指定する三辺の合成関係。 -/
theorem verdierOriginalNativeHomSquare_left (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ verdierOriginalNativeHomSquare d j k =
      SSet.const ((verdierOriginalNativeHomFamily d j).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ coherentTriangleDirectPath)) := by
  have hfirst : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleNativePathIntervalIso.inv.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        ComposableArrows.mk₀ coherentTriangleDirectPath.{u} := by
    apply CategoryTheory.Functor.ext (fun i => ?_)
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathFromInterval (ULift.up (0 : Fin 2)) = coherentTriangleDirectPath
    apply SimplicialThickening.Path.ext
    ext ⟨a⟩
    fin_cases a <;>
      simp [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathFromInterval, coherentTriangleDirectPath, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentOnePath] <;> decide
  rw [verdierOriginalNativeHomSquare, ← Category.assoc, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge, lift_braiding_hom, lift_whiskerLeft, SSet.const_comp, hfirst]
  let z : (Δ[1] : SSet.{u}) ⟶ Δ[0] := SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))
  let r := lift (𝟙 (Δ[1] : SSet.{u})) z
  have h := r ≫= (verdierOriginalNativeHomComparison d j k).prism_restriction
  simpa only [r, z, ← Category.assoc, lift_whiskerLeft, lift_snd,
    coherentTriangleDirectVertexMap, SSet.const_comp, SSet.yonedaEquiv_symm_zero] using! h

end SerrePositivity.KST.Fibration
