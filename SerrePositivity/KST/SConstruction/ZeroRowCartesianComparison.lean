module
public import SerrePositivity.KST.SConstruction.PathBoundaryRealizationPullback
public import SerrePositivity.KST.Comparison.CylinderBoundaryPullback

/-! # 零列写像による行・全対角の厳密な比較
概要：標準零単体との積を外した行評価は既存の零列写像に一致する。
方針：零単体への単体作用素の一意性で射を照合し、積の同型で四角形を移す。
規約：元の零列写像を変更しない。使われ方：経路境界の零行と homotopy fiber の比較。
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

/-- 標準零単体との積を外した行評価は既存の零列写像そのもの。 -/
lemma diagonalZeroColumn_eq_rowEvaluation (F : SimplicialObject SSet.{u}) :
    diagonalZeroColumn F = (simplexZeroTensorIso (F.obj (Opposite.op ⦋0⦌))).inv ≫
      diagonalRowEvaluation F 0 := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro x
  change (F.map (SimplexCategory.const d.unop ⦋0⦌ 0).op).app d x =
    (F.map (stdSimplex.objEquiv _).op).app d x
  congr 3

/-- 零行・全対角の四角形は元の零列写像を使う四角形と同じ homotopy pullback 条件を持つ。 -/
lemma diagonalZeroColumn_homotopyPullback_of_zeroRow {F G : SimplicialObject SSet.{u}}
    (α : F ⟶ G) (h : IsHomotopyPullback
      (CommSq.mk (diagonalRowEvaluation_naturality α 0).symm)) :
    IsHomotopyPullback (CommSq.mk ((diagonalZeroColumnNat.naturality α).symm)) := by
  apply (isHomotopyPullback_iff_of_localized_isIso
    (CommSq.mk ((diagonalZeroColumnNat.naturality α).symm))
    (CommSq.mk (diagonalRowEvaluation_naturality α 0).symm)
    (simplexZeroTensorIso (F.obj (Opposite.op ⦋0⦌))).inv (𝟙 _)
    (simplexZeroTensorIso (G.obj (Opposite.op ⦋0⦌))).inv (𝟙 _)
    ?_ ?_ ?_ ?_ (by infer_instance) (by infer_instance)
    (by infer_instance) (by infer_instance)).mpr h
  · rw [Category.comp_id]
    exact diagonalZeroColumn_eq_rowEvaluation F
  · exact (simplexZeroTensorIso_inv_naturality (α.app (Opposite.op ⦋0⦌))).symm
  · simp only [Category.comp_id, Category.id_comp]
    rfl
  · rw [Category.comp_id]
    exact diagonalZeroColumn_eq_rowEvaluation G

/-- 元の反復経路境界の零行・全対角は零列写像を使って homotopy pullback を与える。 -/
lemma iteratedPathBoundary_zeroRow_homotopyPullback (r : ℕ) (X : StableModel.{u}) :
    IsHomotopyPullback (CommSq.mk
      ((diagonalZeroColumnNat.naturality (iteratedPathBoundary (r + 1) X)).symm)) :=
  diagonalZeroColumn_homotopyPullback_of_zeroRow (iteratedPathBoundary (r + 1) X)
    (iteratedPathBoundary_realization_homotopyPullback r 0 X)

end SerrePositivity.KST.SConstruction
