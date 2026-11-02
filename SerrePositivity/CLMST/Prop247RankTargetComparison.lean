module

public import SerrePositivity.CLMST.Prop247RankAssembly
public import SerrePositivity.BhattScholze.Perfectoidization.FiniteComparisonExcision

/-! # Prop 2.4.7：実 rank 終域比較と指定 canonical excision 比較

成分単位の直積が指定 perfectoid 化であるという実データを受け取り、
元の比較を canonical 誘導写像と同定する。引き戻し性は明示仮定のまま保持する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type} [Finite ι] (T P : ι → Type u)
    [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)]
    [∀ i, CommRing (P i)] [∀ i, Algebra R (P i)]
    (β : ∀ i, T i ⊗[R] S →ₐ[R] P i)

/-- 元の成分普遍単位の実直積写像。 -/
def prop247_rankProductUnit : ((i : ι) → T i ⊗[R] S) →ₐ[R] ((i : ι) → P i) :=
  AlgHom.pi (fun i => (β i).comp (Pi.evalAlgHom R (fun i => T i ⊗[R] S) i))

variable (p : ℕ) [Fact p.Prime] (C : Type u) [CommRing C] [Algebra R C]
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (hβ : ∀ i, IsPerfectoidization p (β i).toRingHom)
    (hProduct : IsPerfectoidization p (prop247_rankProductUnit R S T P β).toRingHom)

/-- 元の実 rank 終域比較は、元の直積単位による canonical 比較そのものである。 -/
theorem prop247_rankPerfectoidComparison_eq_canonical :
    prop247_rankPerfectoidComparison R S T p C f hf P β hβ =
      IsPerfectoidization.mapAlgHom hf hProduct (prop247_rankTensorUnit R S T) := by
  let η := prop247_rankProductUnit R S T P β
  let q := prop247_rankTensorUnit R S T
  let τ := prop247_rankPerfectoidComparison R S T p C f hf P β hβ
  have hτ : τ.comp f = η.comp q := by
    apply AlgHom.ext
    intro s
    exact LinearMap.congr_fun (prop247_rankPerfectoidComparison_square R S T p C f hf P β hβ) s
  obtain ⟨l, _hl, hu⟩ := hf.2 ((i : ι) → P i) hProduct.1 (η.comp q).toRingHom
  apply AlgHom.toRingHom_injective
  exact (hu τ.toRingHom (congrArg AlgHom.toRingHom hτ)).trans
    (hu (IsPerfectoidization.mapAlgHom hf hProduct q).toRingHom
      (congrArg AlgHom.toRingHom (IsPerfectoidization.mapAlgHom_comp hf hProduct q))).symm

/-- 元の canonical excision 四角形から、組立てで必要な実終域比較の核の零化を得る。
直積の普遍性と引き戻し性は実データとして指定し、Cor 8.12 は引用しない。 -/
theorem prop247_rankPerfectoidComparison_ker_of_canonical_excision
    (hR : IsIntegralPerfectoid R p) (g : R)
    (hPB : BhattScholze.KLCanonicalExcisionSquare hf hProduct (prop247_rankTensorUnit R S T) g) :
    ∀ x : (prop247_rankPerfectoidComparison R S T p C f hf P β hβ).toLinearMap.ker,
      g • x = 0 := by
  obtain ⟨hk, _hc⟩ := BhattScholze.perfectoidization_comparison_almost_of_canonical_excision hR hf hProduct
    (prop247_rankTensorUnit R S T) g hPB
  rw [prop247_rankPerfectoidComparison_eq_canonical R S T P β p C f hf hβ hProduct]
  exact hk g (span_le_perfectoidIdeal R p hR g (Ideal.subset_span (Set.mem_singleton g)))

end SerrePositivity.CLMST
