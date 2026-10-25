module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseParameterRecovery
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseRawData
/-!
概要：比較射の像では、逆構成の全混合列が元の余錐族の列に一致する。
方針：パラメーター係数の回収と native 列の成分同値を合成する。
規約：実端点と全整数次数を異種等号で保持する。
使われ方：逆構成した単体データと元の HA 単体の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)
  (y : (dgNerve R (RightModule R D)) _⦋0⦌)

lemma dgCoherentBarInverseMixedColumn_recovery_heq {m : ℕ}
    (c : (coconeMappingSpace F y) _⦋m⦌)
    (L : Finset (Fin (m + 1))) (q : ℤ) (hL : L.Nonempty)
    (hq : q = 1 - (L.card : ℤ)) (l : ℕ) (hcL : L.card = l + 1)
    (s : dgCoherentBarIndex I) :
    HEq (dgCoherentBarInverseMixedColumn R D F hMC (dgNerve.vertexEquiv R (RightModule R D) y)
      (dgCoherentBarCoconeLinearData R D F hMC y c) L q hL hq s)
      (dgCoherentBarCoconeFamilyColumn R D F y
        ((coconeMappingSpace F y).map
          (SimplexCategory.mkHom (L.orderEmbOfFin hcL).toOrderHom).op c) s) := by
  have hql : q = -(l : ℤ) := by rw [hcL] at hq; push_cast at hq; omega
  have hPhi := dgCoherentBarInverseParameterCoefficient_recovery_heq R D F hMC y
    c L q hL hq l hcL
  dsimp only [dgCoherentBarCoconeSubsetParameterHom] at hPhi
  unfold dgCoherentBarInverseMixedColumn
  have hComp := gradedHom_compose_heq (A := R) (D := RightModule R D)
    rfl rfl rfl rfl hql (show q - (s.1 : ℤ) = -(l : ℤ) - (s.1 : ℤ) by omega)
    (p := -(s.1 : ℤ)) (q := q) (k := q - (s.1 : ℤ))
    (p' := -(s.1 : ℤ)) (q' := -(l : ℤ)) (k' := -(l : ℤ) - (s.1 : ℤ))
    (dgCoherentBarInverseParameterCoefficient (dgCoherentBarCoconeLinearData R D F hMC y c)
      L q hL hq) (dgCoherentBarNativeColumn R D F hMC s)
    (dgCoherentBarCoconeFamilyHom R D F hMC y
      ((coconeMappingSpace F y).map
        (SimplexCategory.mkHom (L.orderEmbOfFin hcL).toOrderHom).op c))
    (dgCoherentBarNativeColumn R D F hMC s) hPhi HEq.rfl (by omega) (by omega)
  rw [dgCoherentBarCoconeFamilyHom_columns] at hComp
  exact hComp

end SerrePositivity.InfinityCategories
