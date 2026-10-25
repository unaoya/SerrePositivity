module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseMixedRecovery
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinRawRestrictions
/-!
概要：比較射の像から逆構成した全単体データは、元の余錐族の実 HA 単体に一致する。
方針：左右の純粋な面と全混合成分をそれぞれ回収し、join の外延性を適用する。
規約：候補の任意入力での HA 方程式は別に検証する。
使われ方：全写像空間の逆比較の左逆則。
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

lemma dgCoherentBarInverseRawData_recovery {m n : ℕ}
    (c : (coconeMappingSpace F y) _⦋m⦌) (s : I _⦋n⦌) :
    dgCoherentBarInverseRawData R D F hMC (dgNerve.vertexEquiv R (RightModule R D) y)
      (dgCoherentBarCoconeLinearData R D F hMC y c) s =
    (dgCoherentBarCoconeFamilySimplex R D F y c s).toSimplexData := by
  apply dgCoherentBarJoinSimplexData_ext
  · exact (dgCoherentBarJoinRawData_left _ _ _).trans
      (congrArg DGNerve.Simplex.toSimplexData
        (dgCoherentBarCoconeFamilySimplex_left R D F y c s)).symm
  · have hV : Simplex.vertex (A := R) (dgNerve.vertexEquiv R (RightModule R D) y) = y :=
      (dgNerve.vertexEquiv R (RightModule R D)).symm_apply_apply y
    have hr := dgCoherentBarJoinRawData_right
      (coherentDiagramSimplex F s).toSimplexData
      (InfinityCategories.PinchedHom.constant (X := dgNerve R (RightModule R D))
        (Simplex.vertex (A := R) (dgNerve.vertexEquiv R (RightModule R D) y)) m).toSimplexData
      (dgCoherentBarInverseMixedData R D F hMC (dgNerve.vertexEquiv R (RightModule R D) y)
        (dgCoherentBarCoconeLinearData R D F hMC y c) s)
    exact hr.trans ((congrArg (fun z : (dgNerve R (RightModule R D)) _⦋0⦌ =>
      (InfinityCategories.PinchedHom.constant z m).toSimplexData) hV).trans
        (congrArg DGNerve.Simplex.toSimplexData
          (dgCoherentBarCoconeFamilySimplex_right R D F y c s)).symm)
  · intro K L hK hL a b k hJ ha hb hk
    let r := K.card - 1
    let l := L.card - 1
    have hcK : K.card = r + 1 := by have := Finset.card_pos.mpr hK; dsimp [r]; omega
    have hcL : L.card = l + 1 := by have := Finset.card_pos.mpr hL; dsimp [l]; omega
    have hRaw := dgCoherentBarJoinRawData_mixed_hom_heq
      (coherentDiagramSimplex F s).toSimplexData
      (InfinityCategories.PinchedHom.constant (X := dgNerve R (RightModule R D))
        (Simplex.vertex (A := R) (dgNerve.vertexEquiv R (RightModule R D) y)) m).toSimplexData
      (dgCoherentBarInverseMixedData R D F hMC (dgNerve.vertexEquiv R (RightModule R D) y)
        (dgCoherentBarCoconeLinearData R D F hMC y c) s) K L hK hL a b k hJ ha hb hk
    have hCol := dgCoherentBarInverseMixedColumn_recovery_heq R D F hMC y c L
      (1 - (L.card : ℤ)) hL rfl l hcL (dgCoherentBarSubsetLabel s K r hcK)
    have hMixed : HEq
        (dgCoherentBarInverseMixedData R D F hMC (dgNerve.vertexEquiv R (RightModule R D) y)
          (dgCoherentBarCoconeLinearData R D F hMC y c) s K L hK hL k
          (by rw [dgCoherentBarJoinSubset_card] at hk; push_cast at hk; omega))
        (dgCoherentBarCoconeFamilyColumn R D F y
          ((coconeMappingSpace F y).map
            (SimplexCategory.mkHom (L.orderEmbOfFin hcL).toOrderHom).op c)
          (dgCoherentBarSubsetLabel s K r hcK)) := by
      unfold dgCoherentBarInverseMixedData
      exact (gradedHomTransport_heq (A := R) (D := RightModule R D) _ _ _ _).trans hCol
    exact hRaw.trans (hMixed.trans (dgCoherentBarCoconeFamilySimplex_mixed_hom_heq
      R D F y c s K L hcK hcL a b k hJ ha hb hk).symm)

end SerrePositivity.InfinityCategories
