module
public import SerrePositivity.KST.Fibration.VerdierFullSNativeComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InvertibleEdge

/-!
概要：元の上下長 Hom 比較から、実合成端を結ぶ同じ native core Kan 辺を取り出す。
方針：同じ全 S• 比較の合成 path 成分を取り、元の core 包含と宇宙持ち上げへ送る。
規約：元の比較円柱と実合成端を保持する。別の可逆比較は選ばない。
使われ方：K-6 c4 の読み出した長 Hom 族を、上側の指定合成端へ照合する入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants

namespace SerrePositivity.KST.Fibration
variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2)

/-- 概要：同じ実合成端間の native core Hom の大きい宇宙での実比較辺。
方針：元の全長 Hom 比較を全 path で評価し、同じ元の core 包含で制限する。
規約：下側・上側の実合成端と元の比較円柱を変えない。
使われ方：指定合成端を保つ上側再構成の長 Hom 入力を組み立てる。 -/
def verdierNativeCoreCompositeEdge :=
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge (verdierNullHomFullSNativeComparison d j k).edge)
    (ComposableArrows.mk₀ coherentTriangleFullPath)
  let q := (pre (C := SSet.{u}) (fullSNativeCoreInclusion
    ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩))).app
      ((stableMultiKanEnrichedFunctor 0).obj ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)).obj
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u, u + 1} (e.map q).toTruncated

/-- 概要：元の合成端の同じ native 比較辺は可逆。
方針：元の全比較の可逆性を同じ成分評価・core 制限・宇宙持ち上げへ写す。
規約：整数群の比較や別の存在証人へ置き換えない。
使われ方：同じ長 Hom 入力の合成端を可逆に合わせる。 -/
theorem verdierNativeCoreCompositeEdge_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := (SSet.uliftFunctor.{u + 1, u}).obj
      ((ihom ((stableMultiKanEnrichedFunctor 0).obj
        ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)).obj).obj
          ((stableMultiKanEnrichedFunctor 0).obj
            ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)).obj))
      (verdierNativeCoreCompositeEdge d j k) := by
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.simplicialHomotopyOfFunctorEdge_vertex_isInvertible
    (verdierNullHomFullSNativeComparison d j k).edge
    (verdierNullHomFullSNativeComparison d j k).invertible
    (ComposableArrows.mk₀ coherentTriangleFullPath)
  exact (he.map ((pre (C := SSet.{u}) (fullSNativeCoreInclusion
    ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩))).app
      ((stableMultiKanEnrichedFunctor 0).obj ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)).obj)).ulift

/-- 概要：同じ実合成端比較を再構成が使う core single Kan 座標へ戻す。
方針：元の指定座標同型で Hom の始域と標的を読み替える。
規約：元の比較辺を写すだけで、新しい比較を選ばない。
使われ方：上側・下側の指定長 Hom 空間が持つ同じ core Kan 両端への代入。 -/
def verdierNativeSingleCompositeEdge :=
  let A := (verdierNullDiagonal d).obj ⟨ULift.up 0⟩
  let C := (verdierNullDiagonal d).obj ⟨ULift.up 1⟩
  let q := (pre (C := SSet.{u}) (show (stableCoreSingleKanObject A).obj ⟶
      ((stableMultiKanEnrichedFunctor 0).obj A).obj from (coreSingleKanIso A).hom)).app
      ((stableMultiKanEnrichedFunctor 0).obj C).obj ≫
    (ihom (stableCoreSingleKanObject A).obj).map (coreSingleKanIso C).inv
  (verdierNativeCoreCompositeEdge d j k).map
    ((truncation 2).map ((SSet.uliftFunctor.{u + 1, u}).map q))

/-- 概要：同じ core single Kan 座標での実合成端比較も可逆。
方針：元の可逆辺を同じ座標読み替え写像に送る。
規約：元の両端と比較辺を保持する。
使われ方：再構成入力の指定合成端を可逆に照合する。 -/
theorem verdierNativeSingleCompositeEdge_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := (SSet.uliftFunctor.{u + 1, u}).obj
      ((ihom (stableCoreSingleKanObject
        ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)).obj).obj
          (stableCoreSingleKanObject
            ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)).obj))
      (verdierNativeSingleCompositeEdge d j k) := by
  unfold verdierNativeSingleCompositeEdge
  exact (verdierNativeCoreCompositeEdge_isInvertible d j k).map _

end SerrePositivity.KST.Fibration
