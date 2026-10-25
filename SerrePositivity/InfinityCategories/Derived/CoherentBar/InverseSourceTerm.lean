module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseSourceLeftCut
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseSourceRightCut
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.PostcompositionAlgebra
/-!
概要：逆構成の混合 HA の元の内部頂点の一項を、高次 Hom による native HA 項の後合成へ直す。
方針：削除・左右切断の三つの比較と、全次数合成の結合則と符号を合わせる。
規約：元の theta の微分を変えず、実加群の全 HA 成分を使う。
使われ方：元の単体側の和と高次 Hom の Leibniz 項の相殺。
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
  (N : RightModule R D)

lemma dgCoherentBarInverseFullTerm_source {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) (i : Fin n) :
    HEq (dgCoherentBarFullTerm
      (dgCoherentBarInverseRawData R D F hMC N f s) (i.castAdd m))
      ((m : ℤ).negOnePow •
        compose R (dgCoherentBarInverseFullHomAt R D F hMC N f s)
          (dgCoherentBarFullTerm (dgCoherentBarNativeSimplex R D F hMC s).toSimplexData i)
          (show (-(n : ℤ) + 1) + -(m : ℤ) = -((n + m : ℕ) : ℤ) + 1 by omega)) := by
  let T := (dgCoherentBarInverseRawData R D F hMC N f s)
  let S := (dgCoherentBarNativeSimplex R D F hMC s).toSimplexData
  let ρ := dgCoherentBarInverseFullHomAt R D F hMC N f s
  let p : ℤ := 2 - (((Finset.univ : Finset (Fin (n + 2))).filter
    (· ≤ i.succ.castSucc)).card : ℤ)
  let q : ℤ := 2 - (((Finset.univ : Finset (Fin (n + 2))).filter
    (i.succ.castSucc ≤ ·)).card : ℤ)
  let pT : ℤ := 2 - (((Finset.univ : Finset (Fin (n + m + 2))).filter
    (· ≤ (i.castAdd m).succ.castSucc)).card : ℤ)
  let qT : ℤ := 2 - (((Finset.univ : Finset (Fin (n + m + 2))).filter
    ((i.castAdd m).succ.castSucc ≤ ·)).card : ℤ)
  have hp : pT = p := by
    dsimp only [pT, p]
    rw [dgCoherentBarFullLeft_card, dgCoherentBarFullLeft_card]
    rfl
  have hq : qT = q + -(m : ℤ) := by
    dsimp only [qT, q]
    rw [dgCoherentBarFullRight_card, dgCoherentBarFullRight_card]
    have := i.isLt
    simp only [Fin.val_castAdd]
    omega
  have hkS : p + q = -(n : ℤ) + 1 := by
    dsimp only [p, q]
    rw [dgCoherentBarFullLeft_card, dgCoherentBarFullRight_card]
    have := i.isLt
    omega
  have hkT : pT + qT = -((n + m : ℕ) : ℤ) + 1 := by rw [hp, hq]; omega
  have hFront := (dgCoherentBarInverseRawData_left R D F hMC N f s).trans
    (congrArg DGNerve.Simplex.toSimplexData (dgCoherentBarNativeSimplex_front R D F hMC s)).symm
  have hx0 := congrArg (fun a : DGNerve.SimplexData R (RightModule R D) n => a.obj 0) hFront
  have hx : T.obj 0 = S.obj 0 := hx0
  have hy0 := congrArg
    (fun a : DGNerve.SimplexData R (RightModule R D) n => a.obj i.succ) hFront
  have hy : T.obj (i.castAdd m).succ.castSucc = S.obj i.succ.castSucc := hy0
  have hz : T.obj (Fin.last (n + m + 1)) = N :=
    dgCoherentBarInverseRawData_target R D F hMC N f s
  have hCut := gradedHom_compose_heq (A := R) (D := RightModule R D)
    hx hy hz hp hq rfl
    (dgCoherentBarFullRight T (i.castAdd m)) (dgCoherentBarFullLeft T (i.castAdd m))
    (compose R ρ (dgCoherentBarFullRight S i) rfl) (dgCoherentBarFullLeft S i)
    (dgCoherentBarInverseFullRight_source R D F hMC N f s i)
    (dgCoherentBarInverseFullLeft_source R D F hMC N f s i)
    hkT (show p + (q + -(m : ℤ)) = -((n + m : ℕ) : ℤ) + 1 by omega)
  have hAssoc := DGNerve.compose_assoc_of_sum
    (dgCoherentBarFullLeft S i) (dgCoherentBarFullRight S i) ρ hkS rfl
    (show (-(n : ℤ) + 1) + -(m : ℤ) = -((n + m : ℕ) : ℤ) + 1 by omega)
  change HEq (dgCoherentBarFullTerm T (i.castAdd m))
    ((m : ℤ).negOnePow • compose R ρ (dgCoherentBarFullTerm S i) _)
  rw [dgCoherentBarFullTerm_eq, dgCoherentBarFullTerm_eq,
    DGNerve.compose_units_smul_right, smul_smul,
    ← dgCoherentBarFullTerm_sign_left n m i, DGNerve.compose_sub_right]
  apply dgCoherentBarHom_units_smul_heq hx hz rfl
  apply gradedHom_sub_heq hx hz rfl
  · exact dgCoherentBarInverseFullErase_source R D F hMC N f s i
  · exact hCut.trans (heq_of_eq hAssoc.symm)

end SerrePositivity.InfinityCategories
