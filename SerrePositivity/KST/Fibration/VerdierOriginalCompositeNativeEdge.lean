module
public import SerrePositivity.KST.Fibration.VerdierNativeCompositeEdge
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

set_option maxHeartbeats 800000 in
-- 対象輸送・元の全 Hom 頂点・core Kan 座標の三つの照合を同じ実データに束ねる。
/-- 概要：元の安定比較の同じ実辺を指定両端の core Kan 可逆辺へ送る。
方針：対象等号だけの輸送と元の豊穣作用を連続して適用する。
規約：元の比較辺を保持し、一般の輸送 API は公開しない。
使われ方：指定 Verdier の二実合成を結ぶ大きい宇宙の比較の元データ。 -/
def verdierOriginalCompositeCoreEdgeData (d : VerdierDiagram.{u}) (j k : Fin 2) :
    {e : (SimplicialCategory.sHom
      (stableCoreSingleKanObject (show StableQCat from d.left))
      (stableCoreSingleKanObject (show StableQCat from d.right))).Edge
      (SimplicialCategory.homEquiv' _ _
        (stableCoreSingleKanMap (verdierNullCompositeOriginalMap d j)))
      (SimplicialCategory.homEquiv' _ _
        (stableCoreSingleKanMap (verdierNullCompositeOriginalMap d k))) //
      IsInvertibleEdge e.toTruncated} := by
  let transport {A B A' B' : StableCategory.{u}}
      (hA : A = A') (hB : B = B') (F G : ExactMap A B)
      (e : (SimplicialCategory.sHom (C := StableQCat.{u}) A B).Edge
        (SimplicialCategory.homEquiv' (C := StableQCat.{u}) A B F)
        (SimplicialCategory.homEquiv' (C := StableQCat.{u}) A B G))
      (he : IsInvertibleEdge e.toTruncated) :
      {e' : (SimplicialCategory.sHom (C := StableQCat.{u}) A' B').Edge
        (SimplicialCategory.homEquiv' (C := StableQCat.{u}) A' B' (exactMapTransport hA hB F))
        (SimplicialCategory.homEquiv' (C := StableQCat.{u}) A' B' (exactMapTransport hA hB G)) //
        IsInvertibleEdge e'.toTruncated} := by
    cases hA
    cases hB
    exact ⟨e, he⟩
  have vertex {A B : StableQCat.{u}} (F : ExactMap A B) :
      (stableCoreSingleKanEnrichedFunctor.map A B).app (Opposite.op ⦋0⦌)
        (SimplicialCategory.homEquiv' A B F) =
          SimplicialCategory.homEquiv' (stableCoreSingleKanObject A) (stableCoreSingleKanObject B)
            (stableCoreSingleKanMap F) := by
    exact congrArg (SSet.unitHomEquiv _) (stableCoreSingleKan_hom F)
  let eS := verdierNullCompositeEdge d j k
  let eS' := eS.ofEq
    (stableHom_homEquiv'_ExactMap (verdierNullCompositeVertex d j)).symm
    (stableHom_homEquiv'_ExactMap (verdierNullCompositeVertex d k)).symm
  have heS : IsInvertibleEdge eS'.toTruncated :=
    (isInvertibleEdge_congr (X := ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩ ⟶[SSet.{u}]
      (verdierNullDiagonal d).obj ⟨ULift.up 1⟩))
      (e := eS'.toTruncated) (f := eS.toTruncated) rfl).mpr
      (verdierNullCompositeEdge_isInvertible d j k)
  let p := transport (verdierNullDiagonal_source d) (verdierNullDiagonal_target d)
    (verdierNullCompositeMap d j) (verdierNullCompositeMap d k) eS' heS
  let e := p.val.map (stableCoreSingleKanEnrichedFunctor.map
    (show StableQCat from d.left) (show StableQCat from d.right))
  let e' := e.ofEq (vertex _) (vertex _)
  refine ⟨e', ?_⟩
  exact (isInvertibleEdge_congr (e := e'.toTruncated) (f := e.toTruncated) rfl).mpr
    (p.property.map _)

/-- 概要：元の合成完全射を両端に持つ、指定 Verdier 座標の native core 比較辺。
方針：元の安定比較の同じ対象輸送と core S• 像を宇宙持ち上げする。
規約：元の二合成射と比較円柱を保持する。
使われ方：再構成入力を実上側・実下側の指定合成端へ戻す。 -/
def verdierNativeOriginalCompositeEdge (d : VerdierDiagram.{u}) (j k : Fin 2) :=
  uliftTruncatedEdge.{u, u + 1} (verdierOriginalCompositeCoreEdgeData d j k).val.toTruncated

/-- 概要：同じ指定両端の実合成端比較は可逆。
方針：元の同じ比較の可逆性を対象輸送・core S• 作用・宇宙持ち上げへ写す。
規約：群同型による代用や別の比較辺の存在仮定は使わない。
使われ方：指定合成端間の同じ可逆な照合。 -/
theorem verdierNativeOriginalCompositeEdge_isInvertible (d : VerdierDiagram.{u}) (j k : Fin 2) :
    IsInvertibleEdge (X := (SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (stableCoreSingleKanObject (show StableQCat from d.left))
        (stableCoreSingleKanObject (show StableQCat from d.right))))
      (verdierNativeOriginalCompositeEdge d j k) :=
  (verdierOriginalCompositeCoreEdgeData d j k).property.ulift

/-- 概要：同じ比較辺の下側始端は指定した実包含・実商の合成の core S• Kan 作用。
方針：元の辺の始点と同じ合成完全射の回収式を接続する。
規約：指定包含・商を変えず、元の実一単体を保持する。
使われ方：下側の長 Hom 読出しの実合成端の照合。 -/
theorem verdierNativeOriginalCompositeEdge_lower_source (d : VerdierDiagram.{u}) (k : Fin 2) :
    let H := (SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (stableCoreSingleKanObject (show StableQCat from d.left))
        (stableCoreSingleKanObject (show StableQCat from d.right)))
    H.δ 1 (verdierNativeOriginalCompositeEdge d 1 k).edge =
      ULift.up (SimplicialCategory.homEquiv' _ _
        (stableCoreSingleKanMap (show d.left ⟶ d.right from
          (show d.left ⟶ d.middle from d.inclusion) ≫
            (show d.middle ⟶ d.right from d.projection)))) :=
  (verdierNativeOriginalCompositeEdge d 1 k).src_eq.trans
    (congrArg (fun F : ExactMap d.left d.right => ULift.up
      (SimplicialCategory.homEquiv' _ _ (stableCoreSingleKanMap F)))
        (verdierNullCompositeOriginalMap_lower d))

/-- 概要：同じ比較辺の上側終端は指定した実左辺・実上辺の合成の core S• Kan 作用。
方針：元の辺の終点と同じ上側合成完全射の回収式を接続する。
規約：指定四角形の実二辺と元の比較円柱を保持する。
使われ方：上側再構成が要求する実合成端への照合。 -/
theorem verdierNativeOriginalCompositeEdge_upper_target (d : VerdierDiagram.{u}) (j : Fin 2) :
    let H := (SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (stableCoreSingleKanObject (show StableQCat from d.left))
        (stableCoreSingleKanObject (show StableQCat from d.right)))
    H.δ 0 (verdierNativeOriginalCompositeEdge d j 0).edge =
      ULift.up (SimplicialCategory.homEquiv' _ _ (stableCoreSingleKanMap
        (show d.left ⟶ d.right from (show d.left ⟶ _ from verdierLeftExactMap d) ≫
          (show _ ⟶ d.right from verdierTopExactMap d)))) :=
  (verdierNativeOriginalCompositeEdge d j 0).tgt_eq.trans
    (congrArg (fun F : ExactMap d.left d.right => ULift.up
      (SimplicialCategory.homEquiv' _ _ (stableCoreSingleKanMap F)))
        (verdierNullCompositeOriginalMap_upper d))

end SerrePositivity.KST.Fibration
