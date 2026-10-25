module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftSourceLeftCut
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftSourceRightCut
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.PostcompositionAlgebra
/-!
概要：持ち上げ余錐について、混合 HA の元の内部頂点の一項を、高次 Hom による native HA 項の後合成へ直す。
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

lemma dgCoherentBarCoconeLiftFullTerm_source {m n : ℕ}
    (c : (sliceUnder F) _⦋m⦌) (s : I _⦋n⦌) (i : Fin n) :
    HEq (dgCoherentBarFullTerm
      (dgCoherentBarCoconeLiftSimplex R D F c s).toSimplexData (i.castAdd m))
      ((m : ℤ).negOnePow •
        compose R (dgCoherentBarCoconeLiftHomAt R D F hMC c s)
          (dgCoherentBarFullTerm (dgCoherentBarNativeSimplex R D F hMC s).toSimplexData i)
          (show (-(n : ℤ) + 1) + -(m : ℤ) = -((n + m : ℕ) : ℤ) + 1 by omega)) := by
  let T := (dgCoherentBarCoconeLiftSimplex R D F c s).toSimplexData
  let S := (dgCoherentBarNativeSimplex R D F hMC s).toSimplexData
  let ρ := dgCoherentBarCoconeLiftHomAt R D F hMC c s
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
  have hFront := (dgCoherentBarCoconeLiftSimplex_left R D F c s).trans
    (dgCoherentBarNativeSimplex_front R D F hMC s).symm
  have hx : T.obj 0 = S.obj 0 :=
    congrArg (fun a : DGNerve.Simplex R (RightModule R D) n => a.obj 0) hFront
  have hy : T.obj (i.castAdd m).succ.castSucc = S.obj i.succ.castSucc :=
    congrArg (fun a : DGNerve.Simplex R (RightModule R D) n => a.obj i.succ) hFront
  have hz : T.obj (Fin.last (n + m + 1)) = dgCoherentBarCoconeLiftTarget R D F c :=
    dgCoherentBarCoconeLiftSimplex_target R D F c s
  have hCut := gradedHom_compose_heq (A := R) (D := RightModule R D)
    hx hy hz hp hq rfl
    (dgCoherentBarFullRight T (i.castAdd m)) (dgCoherentBarFullLeft T (i.castAdd m))
    (compose R ρ (dgCoherentBarFullRight S i) rfl) (dgCoherentBarFullLeft S i)
    (dgCoherentBarCoconeLiftFullRight_source R D F hMC c s i)
    (dgCoherentBarCoconeLiftFullLeft_source R D F hMC c s i)
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
  · exact dgCoherentBarCoconeLiftFullErase_source R D F hMC c s i
  · exact hCut.trans (heq_of_eq hAssoc.symm)

end SerrePositivity.InfinityCategories
