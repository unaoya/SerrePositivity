module

public import SerrePositivity.HomologicalAlgebra.HomologyQuotient
public import SerrePositivity.PerfectComplex.TensorResolutionLength
public import SerrePositivity.PerfectComplex.ProjectiveBounds

/-! # 極小性による第零ホモロジーの長さの下界

微分の座標がイデアルに入ることから構成した全射を使う。
Koszul 消滅や Euler 評価はここでは使わず、具体的な代数の入力だけを扱う。
-/

@[expose] public section

universe u

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)

/-- 有限個の同じ加群の直積の長さ。無限長の場合も含む。 -/
lemma NormalizedLength.len_fin_fun (M : Type u) [AddCommGroup M] [Module R M]
    (hM : IsPowTorsion J M) (b : ℕ) : lam.len (Fin b → M) = b * lam.len M := by
  have ht (b : ℕ) : IsPowTorsion J (Fin b → M) := by
    obtain ⟨k, hk⟩ := hM
    exact ⟨k, fun m r ↦ funext fun j ↦ hk (x := m j) (a := r)⟩
  induction b with
  | zero => simp [lam.len_eq_zero_of_subsingleton]
  | succ b ih =>
    rw [lam.len_congr _ _ (Fin.consLinearEquiv R (fun _ : Fin (b + 1) ↦ M)).symm,
      TensorRes.len_prod lam M (Fin b → M) hM (ht b), ih, Nat.cast_succ]
    ring

/-- 極小な零次表示から得られる長さの下界。 -/
lemma lambdaHomology_zero_minimal_lower_bound
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.d 0 1 = 0)
    (I : Ideal R) (hI : IsPowTorsion J (R ⧸ I))
    (b : ℕ) (e : P.X 0 ≅ ModuleCat.of R (Fin b → R))
    (hmin : ∀ m : P.X (-1), ∀ j, e.hom.hom ((P.d (-1) 0).hom m) j ∈ I)
    (ht : IsPowTorsion J (P.homology 0)) :
    b * lam.len (R ⧸ I) ≤ lam.len (P.homology 0) := by
  rw [← lam.len_fin_fun _ hI b]
  exact lam.len_le_of_surjective (minimalHomologyZeroQuotient P hP I b e hmin).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance) ht

/-- 極小性による Koszul 第零ホモロジーの下界。
元の複体の支持や零ホモトピーは要求しない。 -/
lemma lambdaHomology_koszul_zero_minimal_lower_bound
    (hfg : J.FG) {n : ℕ} (x : Fin n → R)
    (hJ : J ≤ (Ideal.span (Set.range x)).radical)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : ∀ q : ℤ, 0 < q → IsZero (P.X q))
    (I : Ideal R) (hI : IsPowTorsion J (R ⧸ I))
    (b : ℕ) (e : P.X 0 ≅ ModuleCat.of R (Fin b → R))
    (hmin : ∀ m : P.X (-1), ∀ j, e.hom.hom ((P.d (-1) 0).hom m) j ∈ I)
    (hx : ∀ j, x j ∈ I) :
    b * lam.len (R ⧸ I) ≤ lam.len ((koszulComplexOn x P).homology 0) := by
  obtain ⟨g, hg⟩ := exists_minimal_koszul_homologyZero_epi P hP I b e hmin x hx
  rw [← lam.len_fin_fun _ hI b]
  exact lam.len_le_of_surjective g.hom ((ModuleCat.epi_iff_surjective _).mp hg)
    (supported_homology_isPowTorsion hfg hJ (isSupported_koszulComplexOn x P) 0)

end SerrePositivity
