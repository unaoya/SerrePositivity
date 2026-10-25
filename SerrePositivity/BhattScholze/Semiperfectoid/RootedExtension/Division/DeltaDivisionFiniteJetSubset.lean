module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaDivisionFiniteJetRegularity
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaRoot.DeltaRootSubsetQuotient

/-! # 同段の任意部分集合のδ関係を追加した実商の比較 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A)
variable (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
variable (hpL : Function.Injective (fun z : RelativeFreeDeltaRing (R := A) σ ↦
  (p : RelativeFreeDeltaRing (R := A) σ) * z))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (d : A) (a : σ → A) (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "I₀" => Ideal.span {(p : L₀), MvPolynomial.C d} ⊔
  deltaDivisionFiniteRelationIdeal D d a (N + 1)
local notation "R₀" => L₀ ⧸ I₀
local notation "Q₀" => DeltaDivisionFiniteNormalizedQuotient D d a v N
local notation "b₀" => deltaDivisionFiniteNormalizedStepCoefficients D d a v N
local notation "f₀" => fun s : σ ↦ Ideal.Quotient.mk I₀
  (deltaDivisionIteratedRelation D d a s (N + 2))
local notation "w₀" => fun s : σ ↦ Ideal.Quotient.mk I₀
  (deltaDivisionRelativeWittRelationElement D d a v s N)

/-- 元の下位δ関係商を最高変数・後続変数を分離した実多項式環へ送る同型。 -/
def deltaDivisionFiniteJetSourceEquiv : R₀ ≃+* MvPolynomial (σ × ℕ) (MvPolynomial σ Q₀) :=
  ((deltaDivisionFiniteNormalizedQuotientEquiv D hpA hpL hg d a v hv N).trans
    (deltaDivisionNormalizedAmbientSourceEquiv D d a v N hv)).trans
    (MvPolynomial.mapEquiv (σ × ℕ) (deltaDivisionNormalizedStepSourceQuotientEquiv D d a v N))

/-- 元のWitt根関係は、最高変数の実根関係の係数像に移る。 -/
theorem deltaDivisionFiniteJetSourceEquiv_witt (s : σ) :
    deltaDivisionFiniteJetSourceEquiv D hpA hpL hg d a v hv N (w₀ s) =
      MvPolynomial.C (deltaRootRelationFamily (p := p) b₀ s) := by
  unfold deltaDivisionFiniteJetSourceEquiv
  rw [RingEquiv.trans_apply, RingEquiv.trans_apply,
    deltaDivisionFiniteNormalizedQuotientEquiv_mk,
    deltaDivisionRelativeWittRelationElement_inverse_image D hpA hg,
    deltaDivisionNormalizedAmbientSourceEquiv_initial, MvPolynomial.mapEquiv_apply,
    MvPolynomial.map_C, RingEquiv.coe_toRingHom,
    deltaDivisionNormalizedStepSourceQuotientEquiv_mk,
    deltaDivisionNormalizedStepPolynomialMap_relation]

include hpL hg hv in
/-- 下位商内では、任意部分集合の次段δ関係とWitt根関係が同じイデアルを生成する。 -/
theorem deltaDivisionFiniteJetSubset_span_eq_witt (T : Set σ) :
    Ideal.span (Set.range fun s : T ↦ f₀ s) =
      Ideal.span (Set.range fun s : T ↦ w₀ s) := by
  let E := relativeFreeDeltaStructure σ D
  let vL := v.map (MvPolynomial.C : A →+* L₀).toMonoidHom
  have hvL : (vL : L₀) = E.delta (MvPolynomial.C d) := by
    change MvPolynomial.C (v : A) = (relativeFreeDeltaStructure σ D).delta (MvPolynomial.C d)
    rw [hv, relativeFreeDeltaStructure_delta_C]
  have hpI : (p : L₀) ∈ I₀ :=
    (show Ideal.span {(p : L₀), MvPolynomial.C d} ≤ I₀ from le_sup_left)
      (Ideal.subset_span (by simp))
  have hdI : MvPolynomial.C d ∈ I₀ :=
    (show Ideal.span {(p : L₀), MvPolynomial.C d} ≤ I₀ from le_sup_left)
      (Ideal.subset_span (by simp))
  have hlower : ∀ s : T, ∀ i ≤ N + 1,
      E.delta^[i] (MvPolynomial.C d * MvPolynomial.X ((s : σ), 0) - MvPolynomial.C (a s)) ∈ I₀ := by
    intro s i hi
    apply (show deltaDivisionFiniteRelationIdeal D d a (N + 1) ≤ I₀ from le_sup_right)
    exact Ideal.subset_span (Set.mem_range.mpr ⟨((s : σ), ⟨i, by omega⟩), rfl⟩)
  have h := congrArg (Ideal.map (Ideal.Quotient.mk I₀))
    (deltaDivision_family_next_jets_sup_span_eq_witt_relations E hpL hg I₀ hpI
      (MvPolynomial.C d) (fun s : T ↦ MvPolynomial.X ((s : σ), 0))
      (fun s : T ↦ MvPolynomial.C (a s)) hdI vL hvL N hlower)
  rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq] at h
  rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq] at h
  simpa [Ideal.map_span, ← Set.range_comp', E, vL,
    deltaDivisionIteratedRelation, deltaDivisionRelativeWittRelationElement] using h

/-- 次段δ関係の部分集合イデアルは、実部分根関係イデアルの係数包含像に移る。 -/
theorem deltaDivisionFiniteJetSubset_map_source (T : Set σ) :
    (Ideal.span (Set.range fun s : T ↦ f₀ s)).map
      (deltaDivisionFiniteJetSourceEquiv D hpA hpL hg d a v hv N).toRingHom =
    (deltaRootSubsetRelationIdeal (p := p) T b₀).map
      (MvPolynomial.C : MvPolynomial σ Q₀ →+* MvPolynomial (σ × ℕ) (MvPolynomial σ Q₀)) := by
  rw [deltaDivisionFiniteJetSubset_span_eq_witt D hpL hg d a v hv N T]
  simp only [Ideal.map_span, ← Set.range_comp', deltaRootSubsetRelationIdeal,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    deltaDivisionFiniteJetSourceEquiv_witt]

/-- 任意先行添字集合の次段δ関係を追加した実商の具体的多項式表示。 -/
def deltaDivisionFiniteJetSubsetQuotientEquiv (T : Set σ) :
    (R₀ ⧸ Ideal.span (Set.range fun s : T ↦ f₀ s)) ≃+*
      MvPolynomial (σ × ℕ) (MvPolynomial σ Q₀ ⧸ deltaRootSubsetRelationIdeal (p := p) T b₀) :=
  (Ideal.quotientEquiv _ _ (deltaDivisionFiniteJetSourceEquiv D hpA hpL hg d a v hv N)
    (deltaDivisionFiniteJetSubset_map_source D hpA hpL hg d a v hv N T).symm).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ × ℕ)
      (deltaRootSubsetRelationIdeal (p := p) T b₀)).symm.toRingEquiv

/-- 部分集合商の同型は、残るWitt関係の標準像を根関係商の係数像へ送る。 -/
theorem deltaDivisionFiniteJetSubsetQuotientEquiv_witt (T : Set σ) (s : σ) :
    deltaDivisionFiniteJetSubsetQuotientEquiv D hpA hpL hg d a v hv N T
      (Ideal.Quotient.mk _ (w₀ s)) =
      MvPolynomial.C (Ideal.Quotient.mk (deltaRootSubsetRelationIdeal (p := p) T b₀)
        (deltaRootRelationFamily (p := p) b₀ s)) := by
  unfold deltaDivisionFiniteJetSubsetQuotientEquiv
  rw [RingEquiv.trans_apply, Ideal.quotientEquiv_mk,
    deltaDivisionFiniteJetSourceEquiv_witt]
  change MvPolynomial.eval₂Hom
    (MvPolynomial.C.comp (Ideal.Quotient.mk (deltaRootSubsetRelationIdeal (p := p) T b₀)))
    MvPolynomial.X (MvPolynomial.C (deltaRootRelationFamily (p := p) b₀ s)) = _
  exact MvPolynomial.eval₂Hom_C _ _ _

include hpA hpL hg hv in
/-- 任意先行部分集合を課しても、集合外のWitt根関係の像は非零因子。 -/
theorem deltaDivisionFiniteJetSubset_witt_isSMulRegular (T : Set σ) (s : σ) (hs : s ∉ T) :
    IsSMulRegular (R₀ ⧸ Ideal.span (Set.range fun t : T ↦ f₀ t))
      (Ideal.Quotient.mk (Ideal.span (Set.range fun t : T ↦ f₀ t)) (w₀ s)) := by
  have hr := deltaRootSubsetQuotient_remaining_isSMulRegular (p := p) T b₀ s hs
  let e := deltaDivisionFiniteJetSubsetQuotientEquiv D hpA hpL hg d a v hv N T
  have he : e (Ideal.Quotient.mk _ (w₀ s)) =
      MvPolynomial.C (Ideal.Quotient.mk (deltaRootSubsetRelationIdeal (p := p) T b₀)
        (deltaRootRelationFamily (p := p) b₀ s)) :=
    deltaDivisionFiniteJetSubsetQuotientEquiv_witt D hpA hpL hg d a v hv N T s
  intro x y hxy
  apply e.injective
  apply MvPolynomial.ext
  intro k
  apply hr
  have h := congrArg (fun z ↦ (e z).coeff k) hxy
  simpa only [smul_eq_mul, map_mul, he, MvPolynomial.coeff_C_mul] using h

include hpA hpL hg hv in
/-- 任意先行部分集合を課しても、集合外の元の次段δ関係の像は非零因子。 -/
theorem deltaDivisionFiniteJetSubset_next_isSMulRegular (T : Set σ) (s : σ) (hs : s ∉ T) :
    IsSMulRegular (R₀ ⧸ Ideal.span (Set.range fun t : T ↦ f₀ t))
      (Ideal.Quotient.mk (Ideal.span (Set.range fun t : T ↦ f₀ t)) (f₀ s)) := by
  have hrange (g : σ → R₀) : Set.range (fun t : ({s} : Set σ) ↦ g t) = {g s} := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      have ht : (t : σ) = s := t.property
      simp only [ht, Set.mem_singleton_iff]
    · intro hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact ⟨⟨s, rfl⟩, rfl⟩
  have he := deltaDivisionFiniteJetSubset_span_eq_witt D hpL hg d a v hv N ({s} : Set σ)
  rw [hrange f₀, hrange w₀] at he
  have h := congrArg (Ideal.map (Ideal.Quotient.mk
    (Ideal.span (Set.range fun t : T ↦ f₀ t)))) he
  simp only [Ideal.map_span, Set.image_singleton] at h
  have hm : Ideal.Quotient.mk (Ideal.span (Set.range fun t : T ↦ f₀ t)) (w₀ s) ∈
      Ideal.span {Ideal.Quotient.mk (Ideal.span (Set.range fun t : T ↦ f₀ t)) (f₀ s)} :=
    h.symm ▸ Ideal.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hm
  have hw : IsRegular (Ideal.Quotient.mk (Ideal.span (Set.range fun t : T ↦ f₀ t)) (w₀ s)) :=
    isLeftRegular_iff_isRegular.mp
      (deltaDivisionFiniteJetSubset_witt_isSMulRegular D hpA hpL hg d a v hv N T s hs)
  rw [hc] at hw
  exact hw.of_mul_left.left

end SerrePositivity.BhattScholze
