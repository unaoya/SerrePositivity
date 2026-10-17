module

public import SerrePositivity.CLMST.Prop247LocalComparison
public import SerrePositivity.CLMST.KLAicTorFromExcision

/-! # Prop 2.4.7：KL と共通の指定 excision 入力から局所実錐へ

KL の既存 API が与える almost 零化を、元の局所分裂の実錐比較へ渡す。
二つの canonical excision 四角形の引き戻し性は明示仮定であり、Cor 8.12 は引用しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open BhattScholze
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- KL の二つの元の canonical 四角形から元の β の錐を冪零化する。
perfectoid 化対象・局所分裂・共通モデルは全て指定データとして保持する。 -/
theorem prop247_fixed_cone_of_two_canonical_excision
    {R A E P Q : Type u} [CommRing R] [CommRing A] [CommRing E]
    [CommRing P] [CommRing Q] [Algebra R A] [Algebra R E] [Algebra R P] [Algebra R Q]
    [Module.Finite R A] [Algebra.FinitePresentation R A]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (β : A →ₐ[R] P) (hβ : IsPerfectoidization p β.toRingHom)
    (η : E →ₐ[R] Q) (hη : IsPerfectoidization p η.toRingHom)
    (d : R) (L : Type u) [CommRing L] [Algebra R L] [IsLocalization (.powers d) L]
    (r : ℕ) (e : L ⊗[R] A ≃ₐ[L] (Fin r → L))
    (a : A →ₐ[R] E) (b : (Fin r → R) →ₐ[R] E)
    (l : E →ₐ[R] (Fin r → L)) [IsLocalizedModule (.powers d) l.toLinearMap]
    (ha : ∀ x, l (a x) = e ((1 : L) ⊗ₜ[R] x))
    (hb : ∀ z i, l (b z) i = algebraMap R L (z i))
    (hfree : IsIntegralPerfectoid (Fin r → R) p)
    (hPBa : KLCanonicalExcisionSquare hβ hη a d)
    (hPBb : KLCanonicalExcisionSquare (f := AlgHom.id R (Fin r → R))
      hfree.isPerfectoidization_id
      hη b d) :
    ∃ q : ℕ, moduleMapConeScalar R β.toLinearMap (d ^ q) = 0 := by
  letI := hR.isReduced R p
  let h := AlgHom.id R (Fin r → R)
  have hh : IsPerfectoidization p h.toRingHom :=
    hfree.isPerfectoidization_id
  have hd : d ∈ perfectoidIdeal R p hR d :=
    span_le_perfectoidIdeal R p hR d (Ideal.subset_span (Set.mem_singleton d))
  obtain ⟨hak, _hac⟩ :=
    perfectoidization_comparison_almost_of_canonical_excision hR hβ hη a d hPBa
  obtain ⟨hbk, hbc⟩ :=
    perfectoidization_comparison_almost_of_canonical_excision hR hh hη b d hPBb
  have heq : IsPerfectoidization.mapAlgHom hh hη b = η.comp b := by
    simpa only [h, AlgHom.comp_id] using IsPerfectoidization.mapAlgHom_comp hh hη b
  rw [heq] at hbk hbc
  apply prop247_fixed_cone_of_localized_splitting p β hβ η hη d L r e a b l ha hb
  · intro y hy
    exact congrArg Subtype.val (hak d hd ⟨y, hy⟩)
  · intro z hz
    exact congrArg Subtype.val (hbk d hd ⟨z, hz⟩)
  · exact hbc d hd

end SerrePositivity.CLMST
