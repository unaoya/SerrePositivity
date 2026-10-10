module

public import SerrePositivity.LengthAlgebra.PerfectHomology
public import SerrePositivity.PerfectComplex.BaseChange
public import SerrePositivity.PerfectComplex.K0Comparison

/-! # 係数変更による有限射影複体の Euler 評価 -/

@[expose] public section

universe u

namespace SerrePositivity.LengthAlgebra

open CategoryTheory CategoryTheory.Limits

variable {R C : Type u} [CommRing R] [CommRing C] (φ : R →+* C)
  {J : Ideal C} (lam : NormalizedLength C J) (hfg : J.FG)
  {e : ℕ} (z : Fin e → R)
  (hJ : J ≤ (Ideal.span (Set.range (φ ∘ z))).radical)
  (hfin : KoszulFinite lam (φ ∘ z))

/-- 係数変更後のホモロジーを長さの商で測る関手。 -/
noncomputable abbrev perfectBaseChangeHomology (q : ℤ) :
    SupportedPerfectHomotopy z ⥤ FiniteLengthQuotient lam :=
  supportedPerfectChangeRing φ z ⋙ perfectQuotientHomology lam hfg (φ ∘ z) hJ hfin q

/-- 三角関手による共通 Euler 評価の引き戻し。 -/
noncomputable def perfectBaseChangeEulerK0 : TriangulatedK0 (SupportedPerfectHomotopy z) →+ ℝ :=
  (perfectEulerK0 lam hfg (φ ∘ z) hJ hfin).comp
    (TriangulatedK0.map (supportedPerfectChangeRing φ z))

/-- 有限自由モデル上でも、新しい Euler 評価は従来の `chiLam` を再現する。 -/
@[simp] lemma perfectBaseChangeEulerK0_free (P : PerfSupp R z) :
    perfectBaseChangeEulerK0 φ lam hfg z hJ hfin
      (TriangulatedK0.mk (perfSuppHomotopyObj P)) = chiLam lam φ P.1 := by
  simp only [perfectBaseChangeEulerK0, AddMonoidHom.comp_apply, TriangulatedK0.map_mk,
    perfectEulerK0_mk]
  exact perfectEuler_eq_lambdaEuler lam hfg (φ ∘ z) hJ hfin _

/-- 旧有限自由 K₀ 上の評価も、共通 Euler 評価から比較写像で引き戻す。 -/
noncomputable def freeBaseChangeEulerK0 : K0Supported R z →+ ℝ :=
  (perfectBaseChangeEulerK0 φ lam hfg z hJ hfin).comp freeToPerfectK0

@[simp] lemma freeBaseChangeEulerK0_mk (P : PerfSupp R z) :
    freeBaseChangeEulerK0 φ lam hfg z hJ hfin (K0.mk P) = chiLam lam φ P.1 := by
  simp [freeBaseChangeEulerK0]

/-- 三角関手の合成に関する自然同型は、Euler 評価の合成にも降りる。 -/
lemma perfectBaseChangeEulerK0_comp {A : Type u} [CommRing A] (α : A →+* R)
    {n : ℕ} (w : Fin n → A)
    (hJ' : J ≤ (Ideal.span (Set.range (φ ∘ α ∘ w))).radical)
    (hfin' : KoszulFinite lam (φ ∘ α ∘ w)) :
    (perfectBaseChangeEulerK0 φ lam hfg (α ∘ w) hJ' hfin').comp
      (TriangulatedK0.map (supportedPerfectChangeRing α w)) =
        perfectBaseChangeEulerK0 (φ.comp α) lam hfg w hJ' hfin' := by
  dsimp only [perfectBaseChangeEulerK0]
  rw [AddMonoidHom.comp_assoc, ← TriangulatedK0.map_comp]
  rw [TriangulatedK0.map_natIso _ (supportedPerfectChangeRingCompIso α w φ)]
  rfl

end SerrePositivity.LengthAlgebra
