module

public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionFiniteResidueRelation
public import SerrePositivity.BhattScholze.Andre.RootedExtension.DeltaRoot.DeltaRootRelationKoszul
public import SerrePositivity.BhattScholze.Andre.RootedExtension.MonicPowerFamilyBaseQuotient

/-! # 最初のδ関係の一般mod(p,d)正則性

初期関係を課したmod(p,d)商を適切な係数商上の多項式環へ移す。
指定単元δdを使うが、正則性・ghost単射・完備性は追加仮定しない。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "J₀" => Ideal.span {(p : L₀), MvPolynomial.C d} ⊔
  deltaDivisionFiniteRelationIdeal D d a 0
local notation "K₀" => deltaDivisionFirstBaseIdeal (p := p) d a

/-- 全深さ0関係を課したmod(p,d)イデアルは、適切な係数イデアルの拡張。 -/
theorem deltaDivisionInitialResidueIdeal_eq_map :
    J₀ = (K₀).map (MvPolynomial.C : A →+* L₀) := by
  rw [deltaDivisionFirstBaseIdeal, Ideal.map_sup, Ideal.map_span, Ideal.map_span]
  simp only [Set.image_pair, map_natCast, ← Set.range_comp']
  apply le_antisymm
  · apply sup_le
    · exact le_sup_left
    · apply Ideal.span_le.mpr
      rintro _ ⟨⟨s, n⟩, rfl⟩
      have hn : n.val = 0 := by omega
      change deltaDivisionIteratedRelation D d a s n.val ∈ _
      rw [hn]
      change MvPolynomial.C d * MvPolynomial.X (s, 0) - MvPolynomial.C (a s) ∈ _
      apply Ideal.sub_mem
      · exact Ideal.mul_mem_right _ _
          ((show Ideal.span {(p : L₀), MvPolynomial.C d} ≤ _ from le_sup_left)
            (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
      · exact (show Ideal.span (Set.range fun t => MvPolynomial.C (a t)) ≤ _ from le_sup_right)
          (Ideal.subset_span (Set.mem_range_self s))
  · apply sup_le
    · exact le_sup_left
    · apply Ideal.span_le.mpr
      rintro _ ⟨s, rfl⟩
      have hg : deltaDivisionIteratedRelation D d a s 0 ∈ J₀ :=
        (show deltaDivisionFiniteRelationIdeal D d a 0 ≤ J₀ from le_sup_right)
          (Ideal.subset_span ⟨(s, 0), rfl⟩)
      have hd : MvPolynomial.C d ∈ J₀ :=
        (show Ideal.span {(p : L₀), MvPolynomial.C d} ≤ J₀ from le_sup_left)
          (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      change MvPolynomial.C d * MvPolynomial.X (s, 0) - MvPolynomial.C (a s) ∈ J₀ at hg
      have h := (J₀).sub_mem ((J₀).mul_mem_right (MvPolynomial.X (s, 0)) hd) hg
      simpa only [sub_sub_cancel, SetLike.mem_coe] using h

/-- 初期mod(p,d)通常商の、適切な係数商上の多項式表示。 -/
def deltaDivisionInitialResiduePolynomialEquiv :
    (L₀ ⧸ J₀) ≃+* MvPolynomial (σ × ℕ) (A ⧸ K₀) :=
  (Ideal.quotEquivOfEq (deltaDivisionInitialResidueIdeal_eq_map D d a)).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial K₀).symm.toRingEquiv

/-- 初期mod(p,d)表示は実自由環の標準像と両立する。 -/
theorem deltaDivisionInitialResiduePolynomialEquiv_mk (f : L₀) :
    deltaDivisionInitialResiduePolynomialEquiv D d a (Ideal.Quotient.mk J₀ f) =
      MvPolynomial.map (Ideal.Quotient.mk K₀) f := by
  rw [deltaDivisionInitialResiduePolynomialEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  exact RingHom.congr_fun (monicPowerFamilyCoefficientQuotient_comp (σ × ℕ) A K₀) f

/-- 初期mod(p,d)商で、最初のδ関係は単元係数を持つ冪関係。 -/
theorem deltaDivisionFirstJet_residue (s : σ) :
    Ideal.Quotient.mk J₀ (deltaDivisionIteratedRelation D d a s 1) =
      Ideal.Quotient.mk J₀ (MvPolynomial.C (D.delta d)) *
        (Ideal.Quotient.mk J₀ (MvPolynomial.X (s, 0))) ^ p -
          Ideal.Quotient.mk J₀ (MvPolynomial.C (D.delta (a s))) := by
  let q := Ideal.Quotient.mk J₀
  have hp : q (p : L₀) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    ((show Ideal.span {(p : L₀), MvPolynomial.C d} ≤ J₀ from le_sup_left)
      (Ideal.subset_span (Set.mem_insert _ _)))
  have hd : q (MvPolynomial.C d) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    ((show Ideal.span {(p : L₀), MvPolynomial.C d} ≤ J₀ from le_sup_left)
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  have ha : q (MvPolynomial.C (a s)) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [deltaDivisionInitialResidueIdeal_eq_map]
    exact Ideal.mem_map_of_mem _ ((show Ideal.span (Set.range a) ≤ K₀ from le_sup_right)
      (Ideal.subset_span (Set.mem_range_self s)))
  have h := deltaDivisionFirstRelation_delta_image (relativeFreeDeltaStructure σ D) q
    (MvPolynomial.C d) (MvPolynomial.X (s, 0)) (MvPolynomial.C (a s)) hp hd ha
  simpa only [deltaDivisionIteratedRelation, Function.iterate_one,
    relativeFreeDeltaStructure_delta_C] using h

/-- 初期係数商の多項式表示は、最初のδ関係を単元倍のモニック冪関係へ送る。 -/
theorem deltaDivisionFirstJet_residue_polynomial (v : Aˣ)
    (hv : (v : A) = D.delta d) (s : σ) :
    let Q := A ⧸ K₀
    let w := v.map (Ideal.Quotient.mk K₀).toMonoidHom
    deltaDivisionInitialResiduePolynomialEquiv D d a
      (Ideal.Quotient.mk J₀ (deltaDivisionIteratedRelation D d a s 1)) =
      MvPolynomial.C (w : Q) *
        (MvPolynomial.X (s, 0) ^ p -
          MvPolynomial.C (((w⁻¹ : Qˣ) : Q) * Ideal.Quotient.mk K₀ (D.delta (a s)))) := by
  let Q := A ⧸ K₀
  let w := v.map (Ideal.Quotient.mk K₀).toMonoidHom
  rw [deltaDivisionFirstJet_residue, map_sub, map_mul, map_pow,
    deltaDivisionInitialResiduePolynomialEquiv_mk,
    deltaDivisionInitialResiduePolynomialEquiv_mk,
    deltaDivisionInitialResiduePolynomialEquiv_mk,
    MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.map_C, ← hv]
  change MvPolynomial.C (w : Q) * MvPolynomial.X (s, 0) ^ p -
    MvPolynomial.C (Ideal.Quotient.mk K₀ (D.delta (a s))) = _
  rw [mul_sub, ← MvPolynomial.C_mul, ← mul_assoc, Units.mul_inv, one_mul]

/-- δdが指定単元なら、最初のδ関係は全深さ0を課したmod(p,d)商上で非零因子。 -/
theorem deltaDivisionFirstJet_residue_isSMulRegular (v : Aˣ)
    (hv : (v : A) = D.delta d) (s : σ) :
    IsSMulRegular (L₀ ⧸ J₀)
      (Ideal.Quotient.mk J₀ (deltaDivisionIteratedRelation D d a s 1)) := by
  let e := deltaDivisionInitialResiduePolynomialEquiv D d a
  let Q := A ⧸ K₀
  let w := v.map (Ideal.Quotient.mk K₀).toMonoidHom
  have he := deltaDivisionFirstJet_residue_polynomial D d a v hv s
  change e (Ideal.Quotient.mk J₀ (deltaDivisionIteratedRelation D d a s 1)) = _ at he
  have hr := deltaRootRelation_isSMulRegular (p := p)
    (fun _ : σ × ℕ => ((w⁻¹ : Qˣ) : Q) * Ideal.Quotient.mk K₀ (D.delta (a s))) (s, 0)
  have hw : IsSMulRegular (MvPolynomial (σ × ℕ) Q) (MvPolynomial.C (w : Q)) :=
    (w.map (MvPolynomial.C : Q →+* MvPolynomial (σ × ℕ) Q).toMonoidHom).isSMulRegular _
  have hreg := hw.mul hr
  intro x y hxy
  apply e.injective
  apply hreg
  have h := congrArg e hxy
  simpa only [smul_eq_mul, map_mul, he, deltaRootRelationFamily] using h

end SerrePositivity.BhattScholze
