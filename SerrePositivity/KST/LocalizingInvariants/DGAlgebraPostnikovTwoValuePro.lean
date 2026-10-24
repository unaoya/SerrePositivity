module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoNonpositiveInverseRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNonpositiveRoofValue

/-!
概要：元の二切断の実両逆を、同じ roof の値による pro 同型へ送る。
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
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {D : Type v} [Category.{w} D] (L : Mon (Complex R) ⥤ D)
  (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
  (h₁ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1)))
  (h₂ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 2)))
include h₀ h₁ h₂

lemma postnikovTwoMap_isProIso (hL : InvertsQuasiIsos R L) :
    IsProIso ((f.map (postnikovFunctor R 2)).map L) := by
  intro i
  obtain ⟨m, hi, ⟨c⟩⟩ := postnikovTwoMap_exists_nonpositiveInverseRoof R f h₀ h₁ h₂ i
  exact ⟨m, hi, c.roof.value R L hL, c.value_triangles R L hL⟩

lemma postnikovTwoMap_isProIso_of_connective (hL : InvertsConnectiveQuasiIsos R L) :
    IsProIso ((f.map (postnikovFunctor R 2)).map L) := by
  intro i
  obtain ⟨m, hi, ⟨c⟩⟩ := postnikovTwoMap_exists_nonpositiveInverseRoof R f h₀ h₁ h₂ i
  exact ⟨m, hi, c.roof.connectiveValue R L hL (postnikov_isConnective R (B.obj m).obj 2),
    c.connectiveValue_triangles R L hL (postnikov_isConnective R (A.obj m).obj 2)
      (postnikov_isConnective R (B.obj m).obj 2) (postnikov_isConnective R (B.obj i).obj 2)⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
