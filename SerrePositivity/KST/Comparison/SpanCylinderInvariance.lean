module

public import SerrePositivity.KST.Comparison.KanReplacementSquares

/-!
# span の射の比較による円筒の四角形の不変性

概要：span の射の可換な比較が各成分で局所化同型なら、円筒の頂点の四角形の性質は変わらない。
方針：円筒の模型の不変性と、四つの頂点のホモトピー引き戻し性の不変性を使う。
規約：Segal 1974 Lemma 1.7 の中間 span を経由する厳密化の比較。
使われ方：成分ごとの局所化同型の zigzag で三頂点の結論を移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe w v u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits
open SerrePositivity.SimplicialModel

/--
概要：二つの射の可換な比較が両関手の下で局所化同型なら、自然性の四角形の性質は同値となる。
方針：自然性と射の比較の等式から四頂点の可換な比較を作る。
規約：関手と自然変換は任意。貼り合わせ定理を仮定しない。
使われ方：span の円筒の頂点の四角形の比較。
-/
theorem naturalitySquare_map_iff {D : Type v} [Category.{w} D] {V T : D ⥤ SSet.{u}}
    (ν : V ⟶ T) {F G F' G' : D} (α : F ⟶ G) (β : F' ⟶ G')
    (u : F ⟶ F') (v : G ⟶ G') (h : α ≫ v = u ≫ β)
    (hVu : IsIso (AnodyneHomotopy.anodyneQ.map (V.map u)))
    (hTu : IsIso (AnodyneHomotopy.anodyneQ.map (T.map u)))
    (hVv : IsIso (AnodyneHomotopy.anodyneQ.map (V.map v)))
    (hTv : IsIso (AnodyneHomotopy.anodyneQ.map (T.map v))) :
    IsHomotopyPullback (naturalitySquare ν α) ↔ IsHomotopyPullback (naturalitySquare ν β) := by
  apply isHomotopyPullback_iff_of_localized_isIso
    (naturalitySquare ν α) (naturalitySquare ν β) (V.map u) (T.map u) (V.map v) (T.map v)
  · exact (ν.naturality u).symm
  · simpa only [V.map_comp] using congrArg V.map h
  · simpa only [T.map_comp] using congrArg T.map h
  · exact (ν.naturality v).symm
  · exact hVu
  · exact hTu
  · exact hVv
  · exact hTv

/--
概要：span の射の比較が各成分で局所化同型なら、円筒への任意の頂点の四角形の性質は同値となる。
方針：評価関手と円筒の関手が比較を局所化同型へ送ることを使う。
規約：元の射と比較後の射の四角形は厳密に可換とする。
使われ方：厳密な span と元の span の中間図式を通す比較。
-/
theorem spanCylinder_vertexSquare_map_iff {F G F' G' : WalkingSpan ⥤ SSet.{u}}
    (α : F ⟶ G) (β : F' ⟶ G') (u : F ⟶ F') (v : G ⟶ G') (h : α ≫ v = u ≫ β)
    (hu : ∀ d, IsIso (AnodyneHomotopy.anodyneQ.map (u.app d)))
    (hv : ∀ d, IsIso (AnodyneHomotopy.anodyneQ.map (v.app d))) (d : WalkingSpan) :
    IsHomotopyPullback (naturalitySquare (spanCylinderVertex d) α) ↔
      IsHomotopyPullback (naturalitySquare (spanCylinderVertex d) β) :=
  naturalitySquare_map_iff (spanCylinderVertex d) α β u v h (hu d)
    (spanCylinderFunctor_map_localized_isIso u hu) (hv d)
    (spanCylinderFunctor_map_localized_isIso v hv)

end SerrePositivity.KST.Comparison
