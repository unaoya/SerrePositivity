module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftParameterLeftCut
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftParameterRightCut
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.FullSimplexComposite
/-!
概要：動く右面の全パラメーター HA 項を、回収した Hom の項と native 列へ分解する。
方針：削除・左右切断の比較を結合則と実符号で合成する。
規約：純粋右面の非零成分を保持し、追加の普遍性を仮定しない。
使われ方：標準 Hom の持ち上げの非線形境界式。
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

lemma dgCoherentBarCoconeLiftFullTerm_parameter {m n : ℕ}
    (c : (sliceUnder F) _⦋m + 1⦌) (s : I _⦋n⦌) (j : Fin (m + 1)) :
    HEq (dgCoherentBarFullTerm
      (dgCoherentBarCoconeLiftSimplex R D F c s).toSimplexData (j.natAdd n))
      (compose R (x := dgCoherentBarSource R D F ⟨n, s⟩)
        (y := dgCoherentBarNormalizedModule R D F hMC)
        (z := dgCoherentBarCoconeLiftTarget R D F c)
        (dgCoherentBarCoconeLiftParameterTerm R D F hMC c j)
        (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩)
        (show -(n : ℤ) + -(m : ℤ) = -((n + (m + 1) : ℕ) : ℤ) + 1 by omega)) := by
  let T := (dgCoherentBarCoconeLiftSimplex R D F c s).toSimplexData
  let U := (sliceUnderProjection F).app (Opposite.op ⦋m + 1⦌) c
  let p : ℤ := 2 - (((Finset.univ : Finset (Fin (n + (m + 1) + 2))).filter
    (· ≤ (j.natAdd n).succ.castSucc)).card : ℤ)
  let q : ℤ := 2 - (((Finset.univ : Finset (Fin (n + (m + 1) + 2))).filter
    ((j.natAdd n).succ.castSucc ≤ ·)).card : ℤ)
  have hp : p = -(n : ℤ) + -(j.val : ℤ) := by
    dsimp only [p]
    rw [dgCoherentBarFullLeft_card]
    simp only [Fin.val_natAdd]
    omega
  have hq : q = (j.val : ℤ) - (m : ℤ) := by
    dsimp only [q]
    rw [dgCoherentBarFullRight_card]
    simp only [Fin.val_natAdd]
    have := j.isLt
    omega
  have hx := dgCoherentBarCoconeLiftSimplex_source R D F c s
  have hz := dgCoherentBarCoconeLiftSimplex_target R D F c s
  have hj : dgCoherentBarJoinRight n (m + 1) j.castSucc =
      (j.natAdd n).succ.castSucc := Fin.ext (by
    change n + 1 + j.val = n + j.val + 1
    omega)
  have hy : T.obj (j.natAdd n).succ.castSucc = U.obj j.castSucc := by
    have h := congrArg (fun a : Simplex R (RightModule R D) (m + 1) => a.obj j.castSucc)
      (dgCoherentBarCoconeLiftSimplex_right R D F c s)
    change T.obj (dgCoherentBarJoinRight n (m + 1) j.castSucc) = _ at h
    rwa [hj] at h
  have hCut := gradedHom_compose_heq (A := R) (D := RightModule R D)
    hx hy hz hp hq rfl
    (p := p) (q := q) (k := -((n + (m + 1) : ℕ) : ℤ) + 1)
    (p' := -(n : ℤ) + -(j.val : ℤ)) (q' := (j.val : ℤ) - (m : ℤ))
    (k' := -((n + (m + 1) : ℕ) : ℤ) + 1)
    (dgCoherentBarFullRight T (j.natAdd n)) (dgCoherentBarFullLeft T (j.natAdd n))
    (dgCoherentBarCoconeLiftParameterTail R D F c j)
    (compose R (dgCoherentBarCoconeLiftParameterPrefix R D F hMC c j)
      (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩) rfl)
    (dgCoherentBarCoconeLiftFullRight_parameter_tail R D F c s j)
    (dgCoherentBarCoconeLiftFullLeft_parameter R D F hMC c s j)
    (by rw [hp, hq]; omega) (by omega)
  have hAssoc := DGNerve.compose_assoc_of_sum
    (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩)
    (dgCoherentBarCoconeLiftParameterPrefix R D F hMC c j)
    (dgCoherentBarCoconeLiftParameterTail R D F c j) rfl
    (show -(j.val : ℤ) + ((j.val : ℤ) - (m : ℤ)) = -(m : ℤ) by omega)
    (show (-(n : ℤ) + -(j.val : ℤ)) + ((j.val : ℤ) - (m : ℤ)) =
      -((n + (m + 1) : ℕ) : ℤ) + 1 by omega)
  unfold dgCoherentBarCoconeLiftParameterTerm
  rw [dgCoherentBarFullTerm_eq_composite, dgCoherentBarFullTerm_sign_right,
    dgCoherentBarFullTerm_sign, DGNerve.compose_units_smul_left, DGNerve.compose_sub_left]
  apply dgCoherentBarHom_units_smul_heq hx hz rfl
  apply gradedHom_sub_heq hx hz rfl
  · exact dgCoherentBarCoconeLiftFullErase_parameter R D F hMC c s j
  · exact hCut.trans (heq_of_eq hAssoc)

end SerrePositivity.InfinityCategories
