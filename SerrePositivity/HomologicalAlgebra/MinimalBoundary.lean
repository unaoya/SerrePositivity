module

public import SerrePositivity.HomologicalAlgebra.MinimalTruncation
public import SerrePositivity.HomologicalAlgebra.TruncationBoundary

/-! # 極小分解の切り詰めの境界と消去元

加群の消去元は射影分解で零ホモトピックになる。切り詰め後の作用は、
直前の Betti 数を階数とする一項複体を経由する。
-/

@[expose] public section

universe u

open CategoryTheory Limits HomologicalComplex

namespace SerrePositivity

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- 加群の消去元の作用は、射影分解で零ホモトピックである。 -/
noncomputable def resolutionScalarNullHomotopy {M : ModuleCat.{u} R}
    (P : ProjectiveResolution M) (r : R) (hr : r • 𝟙 M = 0) :
    Homotopy (r • 𝟙 (extRes P)) 0 := by
  have hc : (r • 𝟙 P.complex) ≫ P.π = 0 := by
    apply HomologicalComplex.Hom.ext
    funext i
    cases i with
    | zero =>
      simp only [smul_f_apply, Linear.smul_comp, Category.id_comp]
      change r • P.π.f 0 = 0
      ext x
      have he := congrArg (fun f : M ⟶ M ↦ f ((P.π.f 0) x)) hr
      exact he
    | succ i =>
      exact (isZero_single_obj_X (ComplexShape.down ℕ) 0 M (i + 1) (by omega)).eq_of_tgt _ _
  have h := (ProjectiveResolution.liftHomotopyZero (P := P) (Q := P) _ hc).extend embUp
  change Homotopy ((embUp.extendFunctor _).map (r • 𝟙 P.complex))
    ((embUp.extendFunctor _).map 0) at h
  simp only [Functor.map_smul, CategoryTheory.Functor.map_id, Functor.map_zero] at h
  exact h

namespace MinimalFreeResolution

variable [IsLocalRing R] [IsNoetherianRing R] (M : FGModuleCat.{u} R) (l : ℕ)

/-- 切り詰めの誤差を担う一項複体。 -/
noncomputable abbrev boundary : CochainComplex (ModuleCat.{u} R) ℤ :=
  TruncationBoundary.boundary (extRes (resolution M)) (-(l : ℤ))

/-- 境界の唯一の項は、極小分解の `l+1` 次の自由項である。 -/
noncomputable def boundaryXIso : (boundary M l).X (-(l : ℤ)) ≅ term M (l + 1) :=
  TruncationBoundary.boundaryXIso _ _ ≪≫
    (complex M).extendXIso embUp (i := l + 1) (by simp; omega)

lemma boundary_isZero_X (q : ℤ) (hq : q ≠ -(l : ℤ)) : IsZero ((boundary M l).X q) :=
  TruncationBoundary.boundary_isZero_X _ _ q hq

instance boundary_free (q : ℤ) : Module.Free R ((boundary M l).X q) := by
  by_cases hq : q = -(l : ℤ)
  · subst q
    exact Module.Free.of_equiv (boundaryXIso M l).toLinearEquiv.symm
  · have := ModuleCat.subsingleton_of_isZero (boundary_isZero_X M l q hq)
    exact Module.Free.of_subsingleton _ _

instance boundary_finite (q : ℤ) : Module.Finite R ((boundary M l).X q) := by
  by_cases hq : q = -(l : ℤ)
  · subst q
    exact Module.Finite.equiv (boundaryXIso M l).toLinearEquiv.symm
  · have := ModuleCat.subsingleton_of_isZero (boundary_isZero_X M l q hq)
    infer_instance

lemma boundary_finrank : Module.finrank R ((boundary M l).X (-(l : ℤ))) =
    MinimalGenerators.rank (syzygy M (l + 1)) := by
  rw [(boundaryXIso M l).toLinearEquiv.finrank_eq]
  change Module.finrank R (Fin (MinimalGenerators.rank (syzygy M (l + 1))) → R) = _
  simp

/-- 切り詰め上の消去元の作用を、直前の自由項を通る射で表す。 -/
lemma scalar_boundary_factorization (r : R) (hr : r • 𝟙 M.obj = 0) :
    ∃ (u : truncated M l ⟶ boundary M l) (v : boundary M l ⟶ truncated M l),
      Nonempty (Homotopy (r • 𝟙 _) (u ≫ v)) :=
  TruncationBoundary.scalar_factorization _ _ r (resolutionScalarNullHomotopy (resolution M) r hr)

end MinimalFreeResolution
end SerrePositivity
