module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovConnectedLevelConnectivity

/-!
概要：元の整数群の pro 連結度から、元の射を保つ連結な実レベル表示を構成する。
方針：有限像模型を元の標的へ引き戻し、非正次数化と全有限切断の実逆を保持する。
規約：比較脚は全整数 π-pro 同値であり、一般 pro ∞ 同値とは同一視しない。
使われ方：LT の連結なレベル表示を、元の dg 代数の実値へ適用する界面。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)}

structure ConnectedLevelRepresentation (f : LevelHom A B) (n : ℤ) where
  middle : Tower (NonpositiveAlgebra R)
  left : LevelHom A middle
  right : LevelHom middle B
  fac : left.comp right = f
  left_connected : ∀ i, IsConnected R (left.app i).hom n
  right_piProEquivalence : IsPiProEquivalence R (right.map (nonpositiveInclusion R))

def connectedLevelRepresentation (f : LevelHom A B) (n : ℤ) (hn : 1 ≤ n)
    (h : IsPiProConnected R (f.map (nonpositiveInclusion R)) n) :
    ConnectedLevelRepresentation R f n where
  middle := PostnikovConnectedLevel.middle R (TowerDiagram.arrowTower f) (n - 1) (by omega)
  left := PostnikovConnectedLevel.left R (TowerDiagram.arrowTower f) (n - 1) (by omega)
  right := PostnikovConnectedLevel.right R (TowerDiagram.arrowTower f) (n - 1) (by omega)
  fac := by
    exact PostnikovConnectedLevel.fac R (TowerDiagram.arrowTower f) (n - 1) (by omega)
  left_connected i := by
    simpa only [sub_add_cancel] using PostnikovConnectedLevel.left_connected R
      (TowerDiagram.arrowTower f) (n - 1) (by omega) i
  right_piProEquivalence := by
    apply PostnikovConnectedLevel.right_piProEquivalence R (TowerDiagram.arrowTower f)
      (n - 1) (by omega)
    rw [PostnikovImagePro.original_arrowTower]
    simpa only [sub_add_cancel] using h

lemma ConnectedLevelRepresentation.right_finite_actual_inverse {f : LevelHom A B} {n : ℤ}
    (c : ConnectedLevelRepresentation R f n) (cutoff : ℤ) (hc : 0 ≤ cutoff) (i : ℕ) :
    ∃ m, ∃ hi : i ≤ m,
      Nonempty (NonpositiveInverseRoof R (c.right.map (postnikovFunctor R cutoff)) i m hi) :=
  postnikovFiniteMap_exists_nonpositiveInverseRoof_int R cutoff hc c.right
    (fun j _ _ => c.right_piProEquivalence j) i

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite LT "Lemma 2.30" (partial := component) "仮定：可換基礎環上の非正 dg 代数の自然数塔、n≥1（Lean が強い）。結論：Postnikov 切断からレベルごとに連結な左脚とプロ同値な右脚の因子分解。一般の Pro(Alg^cn) の同値表示は範囲外（Lean が弱い）。"] _root_.SerrePositivity.KST.LocalizingInvariants.DGAlgebra.connectedLevelRepresentation
