module
public import SerrePositivity.KST.Fibration.VerdierOriginalNativeHomFamily
public import SerrePositivity.KST.Fibration.StableCoreSingleKanHom

/-!
概要：元の合成端比較を指定 Verdier 両端の core single Kan 座標へ厳密に戻す。
方針：元の安定 Hom の比較を対象等号で輸送し、同じ core S• 豊穣作用へ送る。
規約：元の比較辺を保持し、実包含・商や上側合成を別の射へ変更しない。
使われ方：K-6 c4 の同じ指定長 Hom 入力の合成端の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 概要：元の安定比較の同じ実辺を指定両端の core Kan 可逆辺へ送る。
方針：元の全 path 比較を同じ対象輸送へ送り、合成端の成分を回収する。
規約：元の比較辺を保持し、一般の輸送 API は公開しない。
使われ方：指定 Verdier の二実合成を結ぶ大きい宇宙の比較の元データ。 -/
def verdierOriginalCompositeCoreEdgeData (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    {e : (SimplicialCategory.sHom
      (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left))
      (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right))).Edge
      (SimplicialCategory.homEquiv' _ _
        (stableCoreSingleKanMap (verdierNullCompositeOriginalMap d j)))
      (SimplicialCategory.homEquiv' _ _
        (stableCoreSingleKanMap (verdierNullCompositeOriginalMap d k))) //
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e.toTruncated} := by
  let E := verdierOriginalNativeHomComparison d j k
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge E.edge)
    (ComposableArrows.mk₀ coherentTriangleFullPath)
  let e' := e.ofEq (verdierOriginalNativeHomFamily_full d j)
    (verdierOriginalNativeHomFamily_full d k)
  refine ⟨e', ?_⟩
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := e'.toTruncated) (f := e.toTruncated) rfl).mpr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.simplicialHomotopyOfFunctorEdge_vertex_isInvertible E.edge E.invertible _)

/-- 概要：同じ全 path 比較の合成端成分は元の実合成端比較辺そのもの。
方針：同じ元の比較の成分を回収する構成式を使う。
規約：実一単体を保持する。
使われ方：全長 Hom 比較と既存の合成端移送を接続する。 -/
theorem verdierOriginalNativeHomComparison_full_edge (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge (verdierOriginalNativeHomComparison d j k).edge)
      (ComposableArrows.mk₀ coherentTriangleFullPath)).edge =
        (verdierOriginalCompositeCoreEdgeData d j k).val.edge := rfl

/-- 概要：元の合成完全射を両端に持つ、指定 Verdier 座標の native core 比較辺。
方針：元の安定比較の同じ対象輸送と core S• 像を宇宙持ち上げする。
規約：元の二合成射と比較円柱を保持する。
使われ方：再構成入力を実上側・実下側の指定合成端へ戻す。 -/
def verdierNativeOriginalCompositeEdge (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u, u + 1} (verdierOriginalCompositeCoreEdgeData d j k).val.toTruncated

/-- 概要：同じ指定両端の実合成端比較は可逆。
方針：元の同じ比較の可逆性を対象輸送・core S• 作用・宇宙持ち上げへ写す。
規約：群同型による代用や別の比較辺の存在仮定は使わない。
使われ方：指定合成端間の同じ可逆な照合。 -/
theorem verdierNativeOriginalCompositeEdge_isInvertible (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := (SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left))
        (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right))))
      (verdierNativeOriginalCompositeEdge d j k) :=
  (verdierOriginalCompositeCoreEdgeData d j k).property.ulift

/-- 概要：同じ比較辺の下側始端は指定した実包含・実商の合成の core S• Kan 作用。
方針：元の辺の始点と同じ合成完全射の回収式を接続する。
規約：指定包含・商を変えず、元の実一単体を保持する。
使われ方：下側の長 Hom 読出しの実合成端の照合。 -/
theorem verdierNativeOriginalCompositeEdge_lower_source (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (k : Fin 2) :
    let H := (SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left))
        (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)))
    H.δ 1 (verdierNativeOriginalCompositeEdge d 1 k).edge =
      ULift.up (SimplicialCategory.homEquiv' _ _
        (stableCoreSingleKanMap (show d.left ⟶ d.right from
          (show d.left ⟶ d.middle from d.inclusion) ≫
            (show d.middle ⟶ d.right from d.projection)))) :=
  (verdierNativeOriginalCompositeEdge d 1 k).src_eq.trans
    (congrArg (fun F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap d.left d.right => ULift.up
      (SimplicialCategory.homEquiv' _ _ (stableCoreSingleKanMap F)))
        (verdierNullCompositeOriginalMap_lower d))

/-- 概要：同じ比較辺の上側終端は指定した実左辺・実上辺の合成の core S• Kan 作用。
方針：元の辺の終点と同じ上側合成完全射の回収式を接続する。
規約：指定四角形の実二辺と元の比較円柱を保持する。
使われ方：上側再構成が要求する実合成端への照合。 -/
theorem verdierNativeOriginalCompositeEdge_upper_target (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j : Fin 2) :
    let H := (SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left))
        (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)))
    H.δ 0 (verdierNativeOriginalCompositeEdge d j 0).edge =
      ULift.up (SimplicialCategory.homEquiv' _ _ (stableCoreSingleKanMap
        (show d.left ⟶ d.right from (show d.left ⟶ _ from verdierLeftExactMap d) ≫
          (show _ ⟶ d.right from verdierTopExactMap d)))) :=
  (verdierNativeOriginalCompositeEdge d j 0).tgt_eq.trans
    (congrArg (fun F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap d.left d.right => ULift.up
      (SimplicialCategory.homEquiv' _ _ (stableCoreSingleKanMap F)))
        (verdierNullCompositeOriginalMap_upper d))

end SerrePositivity.KST.Fibration
