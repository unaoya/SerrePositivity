module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovFiniteMapValuePro
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovBoundedDerivedPro

/-!
概要：共通下界を持つ元の代数の塔の射を、有限範囲のホモロジー pro 同型から判定する。
方針：有限切断の実逆を値へ送り、元の切断商の準同型正方形で反映する。
規約：有限範囲外の pro 同型やレベルごとの準同型性を仮定しない。
使われ方：bounded-below な切断 pro 判定と連結なレベル表示。
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
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {D : Type v} [Category.{w} D] (L : Mon (Complex R) ⥤ D)

lemma nonpositiveMap_isProIso_of_bounded_connective (hL : InvertsConnectiveQuasiIsos R L)
    (cutoff : ℤ) (hc : 0 ≤ cutoff)
    (hA : ∀ i, (A.obj i).obj.X.IsGE (-cutoff))
    (hB : ∀ i, (B.obj i).obj.X.IsGE (-cutoff))
    (h : ∀ j : ℤ, 0 ≤ j → j ≤ cutoff →
      IsProIso ((f.map (nonpositiveInclusion R)).map (groups R j))) :
    IsProIso ((f.map (nonpositiveInclusion R)).map L) := by
  let a := (postnikovQuotientLevelHom R A cutoff).map L
  let b := (postnikovQuotientLevelHom R B cutoff).map L
  have : ∀ i, IsIso (a.app i) := fun i =>
    hL (by change (A.obj i).obj.X.IsLE 0; infer_instance)
      (postnikov_isConnective R (A.obj i).obj cutoff) _
      (postnikovQuotient_quasiIso R (A.obj i).obj cutoff (hA i))
  have : ∀ i, IsIso (b.app i) := fun i =>
    hL (by change (B.obj i).obj.X.IsLE 0; infer_instance)
      (postnikov_isConnective R (B.obj i).obj cutoff) _
      (postnikovQuotient_quasiIso R (B.obj i).obj cutoff (hB i))
  apply TowerDiagram.proIso_of_square_reverse
    ((f.map (nonpositiveInclusion R)).map L) ((f.map (postnikovFunctor R cutoff)).map L) a b
  · apply ProSpectrum.levelHom_ext
    intro i
    change L.map (f.app i).hom ≫ L.map (postnikovQuotient R (B.obj i).obj cutoff) =
      L.map (postnikovQuotient R (A.obj i).obj cutoff) ≫
        L.map (postnikovMap R (f.app i).hom cutoff)
    rw [← L.map_comp, ← L.map_comp, postnikovQuotient_naturality]
  · exact postnikovFiniteMap_isProIso_of_connective R cutoff hc f L h hL

lemma nonpositiveMap_isProIso_of_bounded (hL : InvertsQuasiIsos R L)
    (cutoff : ℤ) (hc : 0 ≤ cutoff)
    (hA : ∀ i, (A.obj i).obj.X.IsGE (-cutoff))
    (hB : ∀ i, (B.obj i).obj.X.IsGE (-cutoff))
    (h : ∀ j : ℤ, 0 ≤ j → j ≤ cutoff →
      IsProIso ((f.map (nonpositiveInclusion R)).map (groups R j))) :
    IsProIso ((f.map (nonpositiveInclusion R)).map L) :=
  nonpositiveMap_isProIso_of_bounded_connective R f L (hL.connective R L) cutoff hc hA hB h

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
