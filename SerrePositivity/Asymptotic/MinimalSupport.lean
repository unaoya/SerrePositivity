module

public import SerrePositivity.HomologicalAlgebra.MinimalBoundary
public import SerrePositivity.Asymptotic.MinimalResolutionFamily
public import SerrePositivity.Asymptotic.FactorizationSupport

/-! # 極小分解の切り詰めのランク商での支持

切り捨てた直前の Betti 数が `o(s)` なら、その境界複体はランク商で消える。
したがって元の加群列に共通の消去元は、切り詰めた複体列の商での像も消す。
切り詰め自体が分解であることや、切り詰め上の零ホモトピーは要求しない。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory Limits IsLocalRing Filter Asymptotics

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {s : ℕ → ℕ} (M : ℕ → FGModuleCat.{u} R) (l : ℕ)

/-- 直前の Betti 数の `o(s)` は境界複体の全項の `o(s)` を与える。 -/
lemma minimal_boundary_rank_isLittleO
    (hsmall : (fun n ↦ ((Module.length R
      (TorModule R (l + 1) (M n) (R ⧸ maximalIdeal R))).toNat : ℝ))
        =o[atTop] (fun n ↦ (s n : ℝ))) (q : ℤ) :
    (fun n ↦ (Module.finrank R ((MinimalFreeResolution.boundary (M n) l).X q) : ℝ))
      =o[atTop] (fun n ↦ (s n : ℝ)) := by
  by_cases hq : q = -(l : ℤ)
  · subst q
    simp_rw [MinimalFreeResolution.boundary_finrank]
    exact minimal_rank_isLittleO M (l + 1) hsmall
  · apply (isLittleO_zero (fun n ↦ (s n : ℝ)) atTop).congr_left
    intro n
    have := ModuleCat.subsingleton_of_isZero
      (MinimalFreeResolution.boundary_isZero_X (M n) l q hq)
    simp only [Module.finrank_zero_of_subsingleton, Nat.cast_zero]

/-- 境界の族を、小さいランクの実際の自由複体列に組み戻す。 -/
lemma exists_minimal_boundary_sequence
    (hsmall : (fun n ↦ ((Module.length R
      (TorModule R (l + 1) (M n) (R ⧸ maximalIdeal R))).toNat : ℝ))
        =o[atTop] (fun n ↦ (s n : ℝ))) :
    ∃ G : CochainComplex (FreeSequence R s) ℤ,
      rankSmallComplex G ∧ ∀ n,
        Nonempty ((evaluateComplex n).obj G ≅ MinimalFreeResolution.boundary (M n) l) := by
  let P (n : ℕ) := MinimalFreeResolution.boundary (M n) l
  let r (q : ℤ) (n : ℕ) := Module.finrank R ((P n).X q)
  have hr (q : ℤ) : (fun n ↦ (r q n : ℝ)) =o[atTop] (fun n ↦ (s n : ℝ)) :=
    minimal_boundary_rank_isLittleO M l hsmall q
  let e (n : ℕ) (q : ℤ) : ModuleCat.of R (Fin (r q n) → R) ≅ (P n).X q :=
    (Module.finBasis R ((P n).X q)).equivFun.toModuleIso.symm
  refine ⟨assembleComplex P r (fun q ↦ (hr q).isBigO) e,
    assembleComplex_rankSmall P r _ e (-(l : ℤ)) (-(l : ℤ)) ?_ hr,
    fun n ↦ ⟨evaluateAssembleIso P r _ e n⟩⟩
  intro n q hq
  exact MinimalFreeResolution.boundary_isZero_X (M n) l q (by omega)

/-- 共通の消去元は、切り詰めた列の論文のランク商での像を消す。 -/
lemma minimal_truncated_paper_scalar_zero
    (K : CochainComplex (FreeSequence R s) ℤ)
    (hK : strictlyBoundedComplex (FreeSequence R s) K)
    (he : ∀ n, Nonempty ((evaluateComplex n).obj K ≅ MinimalFreeResolution.truncated (M n) l))
    (hsmall : (fun n ↦ ((Module.length R
      (TorModule R (l + 1) (M n) (R ⧸ maximalIdeal R))).toNat : ℝ))
        =o[atTop] (fun n ↦ (s n : ℝ)))
    (r : R) (hM : ∀ n, r • 𝟙 (M n).obj = 0) :
    r • 𝟙 ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)) = 0 := by
  obtain ⟨G, hG, heG⟩ := exists_minimal_boundary_sequence M l hsmall
  have hf : ∀ n, ∃ (u : (evaluateComplex n).obj K ⟶ (evaluateComplex n).obj G)
      (v : (evaluateComplex n).obj G ⟶ (evaluateComplex n).obj K),
      Nonempty (Homotopy (r • 𝟙 _) (u ≫ v)) := by
    intro n
    obtain ⟨e⟩ := he n
    obtain ⟨eG⟩ := heG n
    obtain ⟨u, v, ⟨h⟩⟩ := MinimalFreeResolution.scalar_boundary_factorization (M n) l r (hM n)
    refine ⟨e.hom ≫ u ≫ eG.inv, eG.hom ≫ v ≫ e.inv, ?_⟩
    have ht := (h.compRight e.inv).compLeft e.hom
    simpa only [Linear.smul_comp, Linear.comp_smul, Category.id_comp,
      Category.assoc, Iso.hom_inv_id, Iso.inv_hom_id_assoc] using (Nonempty.intro ht)
  obtain ⟨u, v, ⟨h⟩⟩ := assemble_scalar_factorization K G r hf
  exact paper_scalar_zero_of_small_factorization K G hK hG r u v h

/-- 共通の正の消去指数は、切り詰めの後もランク商での支持を与える。 -/
lemma minimal_truncated_paper_supported {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (FreeSequence R s) ℤ)
    (hK : strictlyBoundedComplex (FreeSequence R s) K)
    (he : ∀ n, Nonempty ((evaluateComplex n).obj K ≅ MinimalFreeResolution.truncated (M n) l))
    (hsmall : (fun n ↦ ((Module.length R
      (TorModule R (l + 1) (M n) (R ⧸ maximalIdeal R))).toNat : ℝ))
        =o[atTop] (fun n ↦ (s n : ℝ)))
    (N : ℕ) (hN : 0 < N) (hM : ∀ n j, z j ^ N • 𝟙 (M n).obj = 0) :
    paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)) :=
  ⟨N, hN, fun j ↦ minimal_truncated_paper_scalar_zero M l K hK he hsmall
    (z j ^ N) (fun n ↦ hM n j)⟩

end SerrePositivity.Asymptotic
