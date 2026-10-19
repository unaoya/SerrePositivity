module
public import SerrePositivity.KST.SConstruction.PathHeadSegalComparison
public import SerrePositivity.KST.Comparison.ProductHomotopyPullback
public import SerrePositivity.KST.Comparison.HomotopyPullbackSymmetry

/-! # 先頭を保つ経路作用素のホモトピー引き戻し
概要：先頭頂点を保つ単体作用素について、元の経路境界の自然性四角形は homotopy pullback。
方針：局所化同型である元の Segal 積座標を使い、任意のファイバーの標準積四角形へ移す。
規約：各行の Kan 性・追加の面条件は要求しない。先頭を飛ばす面は別工程。
使われ方：経路境界の全ての面条件のうち、先頭を保つ場合の供給。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.SimplicialModel SerrePositivity.KST.Comparison
open scoped Simplicial

/-- 先頭頂点を保つ全単体作用素について元の経路境界の自然性四角形は homotopy pullback。 -/
lemma iteratedPathBoundary_headPreserving_homotopyPullback (r : ℕ) {m n : ℕ}
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (hθ : θ.toOrderHom 0 = 0) (X : StableModel.{u}) :
    IsHomotopyPullback (CommSq.mk ((iteratedPathBoundary (r + 1) X).naturality θ.op)) := by
  let f := (iteratedSRealizationDiagram (r + 1) X).map θ.op
  let A := (multiRealizationFunctor (r + 1)).obj (sStableModel 1 X)
  apply (isHomotopyPullback_flip_iff _).mp
  apply (isHomotopyPullback_iff_of_localized_isIso
    (CommSq.mk ((iteratedPathBoundary (r + 1) X).naturality θ.op)).flip
    (productPullbackSquare f A).toCommSq
    (pathHeadSegalMap r n X) (𝟙 _) (pathHeadSegalMap r m X) (𝟙 _)
    ?_ ?_ ?_ ?_
    (pathHeadSegalMap_localized_isIso r n X) (by infer_instance)
    (pathHeadSegalMap_localized_isIso r m X) (by infer_instance)).mpr
  · exact productPullback_isHomotopyPullback f A
  · rw [Category.comp_id, pathHeadSegalMap_fst]
  · exact pathHeadSegalMap_naturality r θ hθ X
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · rw [Category.comp_id, pathHeadSegalMap_fst]

end SerrePositivity.KST.SConstruction
