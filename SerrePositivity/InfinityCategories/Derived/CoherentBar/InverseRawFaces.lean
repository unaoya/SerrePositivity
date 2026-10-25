module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseNativeFactorization
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinRawRestrictions
/-!
概要：逆構成した単体データの左右の面と実端点、全パラメーター係数を固定する。
方針：join 貼り合わせの制限と、左右の包含の頂点公式を使う。
規約：任意の線形成分族に適用する。
使われ方：逆構成の HA 各項の比較。
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

lemma dgCoherentBarInverseRawData_left {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) :
    (dgCoherentBarInverseRawData R D F hMC N f s).pullback (dgCoherentBarJoinLeft n m) =
      (coherentDiagramSimplex F s).toSimplexData := dgCoherentBarJoinRawData_left _ _ _

lemma dgCoherentBarInverseRawData_right {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) :
    (dgCoherentBarInverseRawData R D F hMC N f s).pullback (dgCoherentBarJoinRight n m) =
      (InfinityCategories.PinchedHom.constant (X := dgNerve R (RightModule R D))
        (Simplex.vertex (A := R) N) m).toSimplexData := dgCoherentBarJoinRawData_right _ _ _

lemma dgCoherentBarInverseRawData_source {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) :
    (dgCoherentBarInverseRawData R D F hMC N f s).obj 0 =
      dgCoherentBarSource R D F ⟨n, s⟩ := by
  have h := congrArg (fun t : SimplexData R (RightModule R D) n => t.obj 0)
    (dgCoherentBarInverseRawData_left R D F hMC N f s)
  exact h.trans (coherentDiagramSimplex_obj F s 0)

lemma dgCoherentBarInverseRawData_target {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) :
    (dgCoherentBarInverseRawData R D F hMC N f s).obj (Fin.last (n + m + 1)) = N := by
  have h := congrArg (fun t : SimplexData R (RightModule R D) m => t.obj (Fin.last m))
    (dgCoherentBarInverseRawData_right R D F hMC N f s)
  have he : dgCoherentBarJoinRight n m (Fin.last m) = Fin.last (n + m + 1) :=
    Fin.ext (by dsimp [dgCoherentBarJoinRight, joinRightOrderHom]; omega)
  change (dgCoherentBarInverseRawData R D F hMC N f s).obj
    (dgCoherentBarJoinRight n m (Fin.last m)) = N at h
  rwa [he] at h

abbrev dgCoherentBarInverseFullHom {m : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N m) :=
  dgCoherentBarInverseParameterCoefficient f Finset.univ (-(m : ℤ))
    Finset.univ_nonempty (by simp)

abbrev dgCoherentBarInverseFullHomAt {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) := dgCoherentBarInverseParameterHomAt R D F hMC N f Finset.univ
      (-(m : ℤ)) Finset.univ_nonempty (by simp) s

end SerrePositivity.InfinityCategories
