module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Division.DeltaDivisionFiniteWittFamilyKoszul

/-! # 元のδ次段関係の任意有限族の実残余Koszul分解 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A)
variable (hpA : Function.Injective (fun z : A => (p : A) * z))
variable (hpL : Function.Injective (fun z : RelativeFreeDeltaRing (R := A) σ =>
  (p : RelativeFreeDeltaRing (R := A) σ) * z))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ →
    RelativeFreeDeltaRing (R := A) σ))
variable (d : A) (a : σ → A) (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "I₀" => Ideal.span {(p : L₀), MvPolynomial.C d} ⊔
  deltaDivisionFiniteRelationIdeal D d a (N + 1)
include hpA hpL hg hv

/-- 実下位関係商で、異なる有限個の元のδ次段関係は弱正則列。 -/
theorem deltaDivisionFiniteNextJet_quotient_fin_isWeaklyRegular
    {m : ℕ} (s : Fin m → σ) (hs : Function.Injective s) :
    RingTheory.Sequence.IsWeaklyRegular (L₀ ⧸ I₀)
      (List.ofFn fun i => Ideal.Quotient.mk I₀
        (deltaDivisionIteratedRelation D d a (s i) (N + 2))) := by
  let E := relativeFreeDeltaStructure σ D
  let vL := v.map (MvPolynomial.C : A →+* L₀).toMonoidHom
  have hvL : (vL : L₀) = E.delta (MvPolynomial.C d) := by
    change MvPolynomial.C (v : A) = _
    rw [hv, relativeFreeDeltaStructure_delta_C]
  let f : σ → L₀ ⧸ I₀ := fun t => Ideal.Quotient.mk I₀
    (deltaDivisionIteratedRelation D d a t (N + 2))
  let g : σ → L₀ ⧸ I₀ := fun t => Ideal.Quotient.mk I₀
    (deltaDivisionRelativeWittRelationElement D d a v t N)
  have hspan (t : σ) : Ideal.span {f t} = Ideal.span {g t} := by
    apply deltaDivision_next_jet_quotient_span_eq_witt E hpL hg I₀
      ((show Ideal.span {(p : L₀), MvPolynomial.C d} ≤ I₀ from le_sup_left)
        (Ideal.subset_span (by simp))) (MvPolynomial.C d)
      (MvPolynomial.X (t, 0)) (MvPolynomial.C (a t))
      ((show Ideal.span {(p : L₀), MvPolynomial.C d} ≤ I₀ from le_sup_left)
        (Ideal.subset_span (by simp))) vL hvL N
    intro i hi
    apply (show deltaDivisionFiniteRelationIdeal D d a (N + 1) ≤ I₀ from le_sup_right)
    apply Ideal.subset_span
    exact Set.mem_range.mpr ⟨(t, ⟨i, by omega⟩), rfl⟩
  have hI (l : List σ) : Ideal.ofList (l.map f) = Ideal.ofList (l.map g) := by
    induction l with
    | nil => rfl
    | cons t l ih => simp only [List.map_cons, Ideal.ofList_cons, hspan, ih]
  have hr := deltaDivisionFiniteWittRelation_quotient_fin_isWeaklyRegular
    D d a v N hpA hpL hg hv s hs
  change RingTheory.Sequence.IsWeaklyRegular (L₀ ⧸ I₀) (List.ofFn fun i => f (s i))
  constructor
  intro i hi
  have hi' : i < m := by simpa only [List.length_ofFn] using hi
  have hw := hr.regular_mod_prev i (by simpa only [List.length_ofFn] using hi')
  have hprefix : Ideal.ofList ((List.ofFn fun j => f (s j)).take i) =
      Ideal.ofList ((List.ofFn fun j => g (s j)).take i) := by
    simpa only [List.map_take, List.map_ofFn, Function.comp_def] using
      hI ((List.ofFn s).take i)
  rw [hprefix]
  simp only [List.getElem_ofFn] at hw ⊢
  change IsSMulRegular
    ((L₀ ⧸ I₀) ⧸ (Ideal.ofList ((List.ofFn fun j => g (s j)).take i) • ⊤ :
      Submodule (L₀ ⧸ I₀) (L₀ ⧸ I₀))) (f (s ⟨i, hi'⟩))
  change IsSMulRegular
    ((L₀ ⧸ I₀) ⧸ (Ideal.ofList ((List.ofFn fun j => g (s j)).take i) • ⊤ :
      Submodule (L₀ ⧸ I₀) (L₀ ⧸ I₀))) (g (s ⟨i, hi'⟩)) at hw
  have hm : g (s ⟨i, hi'⟩) ∈ Ideal.span {f (s ⟨i, hi'⟩)} :=
    (hspan _).symm ▸ Ideal.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hm
  intro x y hxy
  apply hw
  change g (s ⟨i, hi'⟩) • x = g (s ⟨i, hi'⟩) • y
  change f (s ⟨i, hi'⟩) • x = f (s ⟨i, hi'⟩) • y at hxy
  rw [hc, mul_comm, mul_smul, mul_smul, hxy]

/-- 同じ実下位関係商上で、実δ次段有限族は通常商のKoszul分解を与える。 -/
theorem deltaDivisionFiniteNextJet_quotient_fin_isKoszulResolution
    {m : ℕ} (s : Fin m → σ) (hs : Function.Injective s) :
    SerrePositivity.IsKoszulResolution (fun i => Ideal.Quotient.mk I₀
      (deltaDivisionIteratedRelation D d a (s i) (N + 2))) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (deltaDivisionFiniteNextJet_quotient_fin_isWeaklyRegular D hpA hpL hg d a v hv N s hs)

end SerrePositivity.BhattScholze
