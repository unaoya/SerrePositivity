module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovFiniteMapValuePro
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovDerivedPro
public import SerrePositivity.KST.LocalizingInvariants.ProInverseSquareNaturality

/-!
概要：有限切断の実逆の値と、元の任意の切断間遷移との整合を証明する。
方針：元の切断正方形と実逆の左三角形を、共通後続段で比較する。
規約：逆 roof の選択は任意。全て元の遷移・脚の値を保持する。
使われ方：有限 Postnikov 比較を bounded-below な塔の切断判定へ接続する。
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
variable (R : Type u) [CommRing R] (a b : ℤ) (hab : b ≤ a)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {D : Type v} [Category.{w} D] (L : Mon (Complex R) ⥤ D)

lemma postnikovFiniteMap_transition_square :
    ((f.map (postnikovFunctor R a)).map L).comp
        ((postnikovTransitionLevelHom R B a b hab).map L) =
      ((postnikovTransitionLevelHom R A a b hab).map L).comp
        ((f.map (postnikovFunctor R b)).map L) := by
  apply ProSpectrum.levelHom_ext
  intro i
  change L.map (postnikovMap R (f.app i).hom a) ≫
      L.map (postnikovTransition R (B.obj i).obj a b hab) =
    L.map (postnikovTransition R (A.obj i).obj a b hab) ≫
      L.map (postnikovMap R (f.app i).hom b)
  rw [← L.map_comp, ← L.map_comp, postnikovTransition_naturality]

lemma postnikovFiniteInverse_values_transition (hb : 0 ≤ b)
    (h : ∀ j : ℤ, 0 ≤ j → j ≤ a →
      IsProIso ((f.map (nonpositiveInclusion R)).map (groups R j)))
    (hL : InvertsConnectiveQuasiIsos R L) {i m l : ℕ} {hi : i ≤ m} {hj : i ≤ l}
    (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R a)) i m hi)
    (d : NonpositiveInverseRoof R (f.map (postnikovFunctor R b)) i l hj) :
    ∃ k, ∃ hm : m ≤ k, ∃ hl : l ≤ k,
      (((B.map (postnikovFunctor R a)).map L).transition hm ≫
        c.roof.connectiveValue R L hL (postnikov_isConnective R (B.obj m).obj a)) ≫
          L.map (postnikovTransition R (A.obj i).obj a b hab) =
      (((B.map (postnikovFunctor R a)).map L).transition hl ≫
        L.map (postnikovTransition R (B.obj l).obj a b hab)) ≫
          d.roof.connectiveValue R L hL (postnikov_isConnective R (B.obj l).obj b) := by
  have hc := (c.connectiveValue_triangles R L hL
    (postnikov_isConnective R (A.obj m).obj a)
    (postnikov_isConnective R (B.obj m).obj a)
    (postnikov_isConnective R (B.obj i).obj a)).1
  have hd := (d.connectiveValue_triangles R L hL
    (postnikov_isConnective R (A.obj l).obj b)
    (postnikov_isConnective R (B.obj l).obj b)
    (postnikov_isConnective R (B.obj i).obj b)).1
  exact TowerDiagram.inverse_square_eventually
    ((f.map (postnikovFunctor R a)).map L) ((f.map (postnikovFunctor R b)).map L)
    ((postnikovTransitionLevelHom R A a b hab).map L)
    ((postnikovTransitionLevelHom R B a b hab).map L)
    (postnikovFiniteMap_isProIso_of_connective R a (hb.trans hab) f L h hL)
    (postnikovFiniteMap_transition_square R a b hab f L) hi hj _ _ hc hd

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
