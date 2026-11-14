module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovFiniteNonpositiveInverseInduction
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNonpositiveRoofValue

/-!
概要：元の有限切断の実両逆を、同じ roof の値による pro 同型へ送る。
方針：実左細分と元の右経路の像から得た両三角形をそのまま使う。
規約：値の逆を選び直さない。使われ方：有限切断と局所化不変量値の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] (cutoff : ℤ) (hc : 0 ≤ cutoff) {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {D : Type v} [Category.{w} D] (L : Mon (Complex R) ⥤ D)
  (h : ∀ j : ℤ, 0 ≤ j → j ≤ cutoff →
    IsProIso ((f.map (nonpositiveInclusion R)).map (groups R j)))
include h hc

lemma postnikovFiniteMap_isProIso (hL : InvertsQuasiIsos R L) :
    IsProIso ((f.map (postnikovFunctor R cutoff)).map L) := by
  intro i
  obtain ⟨m, hi, ⟨c⟩⟩ := postnikovFiniteMap_exists_nonpositiveInverseRoof_int R cutoff hc f h i
  exact ⟨m, hi, c.roof.value R L hL, c.value_triangles R L hL⟩

lemma postnikovFiniteMap_isProIso_of_connective (hL : InvertsConnectiveQuasiIsos R L) :
    IsProIso ((f.map (postnikovFunctor R cutoff)).map L) := by
  intro i
  obtain ⟨m, hi, ⟨c⟩⟩ := postnikovFiniteMap_exists_nonpositiveInverseRoof_int R cutoff hc f h i
  exact ⟨m, hi, c.roof.connectiveValue R L hL (postnikov_isConnective R (B.obj m).obj cutoff),
    c.connectiveValue_triangles R L hL (postnikov_isConnective R (A.obj m).obj cutoff)
      (postnikov_isConnective R (B.obj m).obj cutoff) (postnikov_isConnective R (B.obj i).obj cutoff)⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite LT "Lemma 2.28" (partial := component) "仮定：非正 dg 代数の自然数塔と連結準同型を反転する関手（Lean が強い）。結論：有界切断の各次数のプロ同型から切断値のプロ同型。一般のプロ加群・環の忘却関手の保存性は対象外（Lean が弱い）。"] _root_.SerrePositivity.KST.LocalizingInvariants.DGAlgebra.postnikovFiniteMap_isProIso_of_connective
