module
public import SerrePositivity.KST.Fibration.VerdierNativeCompositeEdge
public import SerrePositivity.KST.Fibration.StableCoreSingleKanHom

/-!
概要：元の上下長 Hom と同じ固定対角比較を、指定 Verdier 両端の native Kan Hom へ戻す。
方針：元の安定 Hom 全体を対象等号で輸送してから同じ core S• 豊穣作用へ送る。
規約：全 path と元の比較辺を保持し、合成端だけの比較へ弱めない。
使われ方：K-6 c4 の有限端点における指定全長 Hom の照合。
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

/-- 概要：元の指定両端の小さい宇宙での core Kan Hom。
方針：元の core S• の豊穣 Hom を使う。
規約：再構成用の宇宙持ち上げ前の全 path 比較を保持する。
使われ方：元の上下 native 長 Hom 全族の共通標的。 -/
abbrev verdierOriginalNativeHomTarget (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :=
  SimplicialCategory.sHom
    (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left))
    (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right))

/-- 概要：元の共有対角の安定 Hom 全体を、指定両端の core Kan Hom へ送る。
方針：同じ二端点の厳密等号で輸送し、元の豊穣作用を後合成する。
規約：元の長 Hom や比較を選び直さない。
使われ方：元の上下全 path 族と固定直接端比較の共通輸送。 -/
def verdierOriginalNativeHomMap (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩ ⟶[SSet.{u}]
      (verdierNullDiagonal d).obj ⟨ULift.up 1⟩) ⟶ verdierOriginalNativeHomTarget d :=
  eqToHom (congrArg₂ (fun (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) =>
    SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) A B)
      (verdierNullDiagonal_source d) (verdierNullDiagonal_target d)) ≫
    stableCoreSingleKanEnrichedFunctor.map
      (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left) (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)

/-- 概要：元の上下全長 Hom を指定 Verdier 両端で読む同じ全 path 族。
方針：元の安定 Hom 族を共通輸送へ送る。
規約：元の全 path を保持する。
使われ方：有限端点で保持する上側・下側の指定 native Hom。 -/
def verdierOriginalNativeHomFamily (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j : Fin 2) :=
  verdierNullHomFamily d j ≫ verdierOriginalNativeHomMap d

/-- 概要：同じ元の上下 native Hom 族を、直接端上で恒等の実可逆辺で比較する。
方針：元の固定直接端比較を同じ対象輸送と豊穣作用へ送る。
規約：別の比較辺の存在を仮定しない。
使われ方：有限入力点の実上側全長 Hom を合成端比較とともに回収する。 -/
def verdierOriginalNativeHomComparison (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    FixedRestrictionFunctorEdge coherentTriangleDirectVertexMap
      (verdierOriginalNativeHomFamily d j) (verdierOriginalNativeHomFamily d k) :=
  (verdierNullHomRelativeComparison d j k).postcomp (verdierOriginalNativeHomMap d)

private theorem nativeHom_transport_vertex {A B A' B' : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (hA : A = A') (hB : B = B') (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) :
    (eqToHom (congrArg₂ (fun (X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) =>
      SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) X Y) hA hB)).app (Opposite.op ⦋0⦌)
        (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) A B F) =
      SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) A' B'
        (exactMapTransport hA hB F) := by
  cases hA
  cases hB
  rfl

/-- 概要：同じ全 path 族の合成端は、元の実合成完全射の指定 core Kan 頂点。
方針：元の全長 Hom の合成点を同じ対象輸送と豊穣頂点回収へ渡す。
規約：元の二合成射を保持する。
使われ方：元の全 path 比較と構成済み実合成端比較の接続。 -/
theorem verdierOriginalNativeHomFamily_full (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j : Fin 2) :
    (verdierOriginalNativeHomFamily d j).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ coherentTriangleFullPath) =
      SimplicialCategory.homEquiv' _ _
        (stableCoreSingleKanMap (verdierNullCompositeOriginalMap d j)) := by
  let h := congrArg₂ (fun (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) =>
    SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) A B)
      (verdierNullDiagonal_source d) (verdierNullDiagonal_target d)
  change (stableCoreSingleKanEnrichedFunctor.map _ _).app (Opposite.op ⦋0⦌)
    ((eqToHom h).app (Opposite.op ⦋0⦌) (verdierNullCompositeVertex d j)) = _
  rw [← stableHom_homEquiv'_ExactMap (verdierNullCompositeVertex d j),
    nativeHom_transport_vertex]
  exact congrArg (SSet.unitHomEquiv _) (stableCoreSingleKan_hom
    (verdierNullCompositeOriginalMap d j))

/-- 概要：同じ元の全族比較は直接 path 上で厳密に一致する。
方針：元の共有対角の一致を同じ全 Hom 輸送へ後合成する。
規約：直接端の代表を選び直さない。
使われ方：指定全長 Hom の比較を固定始端付きの区間比較へ読む。 -/
theorem verdierOriginalNativeHomFamily_same_direct (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    coherentTriangleDirectVertexMap ≫ verdierOriginalNativeHomFamily d j =
      coherentTriangleDirectVertexMap ≫ verdierOriginalNativeHomFamily d k := by
  simpa only [verdierOriginalNativeHomFamily, ← Category.assoc] using
    congrArg (fun f => f ≫ verdierOriginalNativeHomMap d)
      (verdierNullHomFamily_same_direct d j k)

end SerrePositivity.KST.Fibration
