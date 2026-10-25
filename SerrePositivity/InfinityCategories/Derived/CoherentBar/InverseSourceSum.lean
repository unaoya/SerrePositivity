module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseSourceTerm
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeFullCoefficient
/-!
概要：逆構成の混合 HA 右辺の元の単体側の和を、高次 Hom と native 列の微分の合成へ同定する。
方針：全項の因数分解を有限和へ束ね、native 単体の実 HA 方程式を適用する。
規約：内部頂点のない元の単体も含む。
使われ方：Hom の Leibniz 項と HA 右辺の元の単体側を相殺する。
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

lemma dgCoherentBarInverse_source_sum {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) :
    HEq (∑ i : Fin n, dgCoherentBarFullTerm
      (dgCoherentBarInverseRawData R D F hMC N f s) (i.castAdd m))
      ((m : ℤ).negOnePow •
        compose R (x := dgCoherentBarSource R D F ⟨n, s⟩)
          (y := dgCoherentBarNormalizedModule R D F hMC)
          (z := N)
          (dgCoherentBarInverseFullHom R D F hMC N f)
          (differential R (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩))
          (show (-(n : ℤ) + 1) + -(m : ℤ) = -((n + m : ℕ) : ℤ) + 1 by omega)) := by
  let T := (dgCoherentBarInverseRawData R D F hMC N f s)
  let S := (dgCoherentBarNativeSimplex R D F hMC s).toSimplexData
  let ρ := dgCoherentBarInverseFullHomAt R D F hMC N f s
  have hFront := (dgCoherentBarInverseRawData_left R D F hMC N f s).trans
    (congrArg DGNerve.Simplex.toSimplexData (dgCoherentBarNativeSimplex_front R D F hMC s)).symm
  have hx0 := congrArg (fun a : DGNerve.SimplexData R (RightModule R D) n => a.obj 0) hFront
  have hx : T.obj 0 = S.obj 0 := hx0
  have hz : T.obj (Fin.last (n + m + 1)) = N :=
    dgCoherentBarInverseRawData_target R D F hMC N f s
  have hSum := sum_heq_of_obj_eq hx hz
    (fun i : Fin n => dgCoherentBarFullTerm T (i.castAdd m))
    (fun i : Fin n => (m : ℤ).negOnePow •
      compose R ρ (dgCoherentBarFullTerm S i)
        (show (-(n : ℤ) + 1) + -(m : ℤ) = -((n + m : ℕ) : ℤ) + 1 by omega))
    (fun i => dgCoherentBarInverseFullTerm_source R D F hMC N f s i)
  rw [← Finset.smul_sum, ← DGNerve.compose_sum_right,
    ← dgCoherentBarFullSimplex_equation (dgCoherentBarNativeSimplex R D F hMC s)] at hSum
  have hxs := dgCoherentBarNativeSimplex_source R D F hMC s
  have hys := dgCoherentBarNativeSimplex_last R D F hMC s
  have hd := gradedHom_differential_heq (A := R) (D := RightModule R D) hxs hys rfl _ _
    (dgCoherentBarNativeSimplex_full_hom_heq R D F hMC s)
  have hComp := gradedHom_compose_heq (A := R) (D := RightModule R D)
    hxs hys rfl rfl rfl rfl
    (p := -(n : ℤ) + 1) (q := -(m : ℤ)) (k := -((n + m : ℕ) : ℤ) + 1)
    (p' := -(n : ℤ) + 1) (q' := -(m : ℤ)) (k' := -((n + m : ℕ) : ℤ) + 1)
    ρ
    (differential R ((dgCoherentBarNativeSimplex R D F hMC s).hom Finset.univ
      0 (Fin.last (n + 1)) (-(n : ℤ)) (coherentDiagramTop_card n)
      (coherentDiagramTop_min n) (coherentDiagramTop_max n) (by simp; omega)))
    (dgCoherentBarInverseFullHom R D F hMC N f)
    (differential R (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩))
    (dgCoherentBarInverseParameterHomAt_heq R D F hMC N f Finset.univ
      (-(m : ℤ)) Finset.univ_nonempty (by simp) s) hd (by omega) (by omega)
  refine hSum.trans ?_
  exact dgCoherentBarHom_units_smul_heq hxs rfl rfl (m : ℤ).negOnePow _ _ hComp

end SerrePositivity.InfinityCategories
