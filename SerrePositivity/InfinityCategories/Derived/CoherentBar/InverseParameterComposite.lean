module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseParameterLeftCut
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseParameterRightCut
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.FullSimplexComposite
/-!
概要：逆構成のパラメーター側の HA 切断合成は最後以外で零、最後では最終面の高次 Hom となる。
方針：定値側の右因子を零または単位へ同定し、全次数の合成則を適用する。
規約：実際の切断点の対象と次数の輸送を明示する。
使われ方：パラメーター側の有限和を標準面の境界式へまとめる。
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
  (hMC : dgCoherentBarMaurerCartan R D F) (N : RightModule R D)

lemma dgCoherentBarInverseRawData_parameter_obj {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) (a : Fin (m + 1)) :
    (dgCoherentBarInverseRawData R D F hMC N f s).obj (dgCoherentBarJoinRight n m a) =
      N :=
  by
    have h := congrArg (fun t : DGNerve.SimplexData R (RightModule R D) m => t.obj a)
      (dgCoherentBarInverseRawData_right R D F hMC N f s)
    exact h

lemma dgCoherentBarInverseFullComposite_parameter_zero {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N (m + 1))
    (s : I _⦋n⦌) (j : Fin (m + 1))
    (hj : j ≠ Fin.last m) :
    dgCoherentBarFullComposite
      (dgCoherentBarInverseRawData R D F hMC N f s) (j.natAdd n) = 0 := by
  let T := (dgCoherentBarInverseRawData R D F hMC N f s)
  have hpos : dgCoherentBarJoinRight n (m + 1) j.castSucc =
      (j.natAdd n).succ.castSucc := Fin.ext (by
    change n + 1 + j.val = n + j.val + 1
    omega)
  have hy : T.obj (j.natAdd n).succ.castSucc = N := by
    rw [← hpos]
    exact dgCoherentBarInverseRawData_parameter_obj R D F hMC N f s j.castSucc
  have hz := dgCoherentBarInverseRawData_target R D F hMC N f s
  have hq : (2 - (((Finset.univ : Finset (Fin (n + (m + 1) + 2))).filter
      ((j.natAdd n).succ.castSucc ≤ ·)).card : ℤ)) =
      2 - ((dgCoherentBarParameterTail j).card : ℤ) := by
    rw [dgCoherentBarFullRight_card, dgCoherentBarParameterTail_card]
    simp only [Fin.val_natAdd]
    have := j.isLt
    omega
  have hZero := gradedHom_zero_heq (A := R) (D := RightModule R D) hy hz hq
  have hRight : dgCoherentBarFullRight T (j.natAdd n) = 0 :=
    eq_of_heq ((dgCoherentBarInverseFullRight_parameter_zero R D F hMC N f s j hj).trans
      hZero.symm)
  change compose R (dgCoherentBarFullRight T (j.natAdd n))
    (dgCoherentBarFullLeft T (j.natAdd n)) _ = 0
  rw [hRight, DGNerve.zero_compose]

lemma dgCoherentBarInverseFullComposite_parameter_last
    {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N (m + 1))
    (s : I _⦋n⦌) :
    HEq (dgCoherentBarFullComposite
      (dgCoherentBarInverseRawData R D F hMC N f s) ((Fin.last m).natAdd n))
      (compose R (x := dgCoherentBarSource R D F ⟨n, s⟩)
        (y := dgCoherentBarNormalizedModule R D F hMC)
        (z := N)
        (dgCoherentBarInverseFaceHom R D F hMC N f (Fin.last (m + 1)))
        (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩)
        (show -(n : ℤ) + -(m : ℤ) = -((n + (m + 1) : ℕ) : ℤ) + 1 by omega)) := by
  let T := (dgCoherentBarInverseRawData R D F hMC N f s)
  let j := (Fin.last m).natAdd n
  have hpos : dgCoherentBarJoinRight n (m + 1) (Fin.last m).castSucc = j.succ.castSucc :=
    Fin.ext (by change n + 1 + m = n + m + 1; omega)
  have hy : T.obj j.succ.castSucc = N := by
    rw [← hpos]
    exact dgCoherentBarInverseRawData_parameter_obj R D F hMC N f s (Fin.last m).castSucc
  have hz := dgCoherentBarInverseRawData_target R D F hMC N f s
  have hq : (2 - (((Finset.univ : Finset (Fin (n + (m + 1) + 2))).filter
      (j.succ.castSucc ≤ ·)).card : ℤ)) = 0 := by
    rw [dgCoherentBarFullRight_card]
    simp only [j, Fin.val_natAdd, Fin.val_last]
    omega
  have hUnit := DGNerve.unit_compose_of_heq (A := R)
    (k := -((n + (m + 1) : ℕ) : ℤ) + 1)
    (dgCoherentBarFullRight T j) (dgCoherentBarFullLeft T j)
    (by rw [dgCoherentBarFullLeft_card, dgCoherentBarFullRight_card]
        simp only [j, Fin.val_natAdd, Fin.val_last]
        omega)
    (hy.trans hz.symm) hq
    ((dgCoherentBarInverseFullRight_parameter_unit R D F hMC N f s).trans
      (dgCoherentBarHom_unit_heq hz.symm))
  refine hUnit.trans ((dgCoherentBarInverseFullLeft_parameter_last R D F hMC N f s).trans ?_)
  exact dgCoherentBarHom_compose_degree_heq (R := R)
    (p := -(n : ℤ)) (q := -(m : ℤ)) (k := -(n : ℤ) + -(m : ℤ))
    (l := -((n + (m + 1) : ℕ) : ℤ) + 1)
    (a := dgCoherentBarSource R D F ⟨n, s⟩) (b := dgCoherentBarNormalizedModule R D F hMC)
    (c := N)
    (dgCoherentBarInverseFaceHom R D F hMC N f (Fin.last (m + 1)))
    (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩) rfl (by omega)

end SerrePositivity.InfinityCategories
