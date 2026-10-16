module

public import SerrePositivity.BhattScholze.DeltaDivisionFiniteEvaluationRelations
public import SerrePositivity.CommutativeAlgebra.KoszulResolution

/-! # 任意有限根族の次段δ関係から実評価関係への移送 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
variable {T : Type v} [CommRing T] (q : RelativeFreeDeltaRing (R := A) σ →+* T)
variable (N : ℕ) (hI : deltaDivisionFiniteRelationIdeal D d a N ≤ RingHom.ker q)
include hI

/-- 下位関係を消す通常射の後で、次の実評価・δ反復関係は同じ主イデアルを生成する。 -/
theorem deltaDivisionMappedNextEvaluation_span_eq (t : σ) :
    Ideal.span {q (deltaDivisionEvaluationRelation D d a t (N + 1))} =
      Ideal.span {q (deltaDivisionIteratedRelation D d a t (N + 1))} := by
  have h := congrArg (Ideal.map q) (deltaDivisionEvaluation_next_sup_span_eq D d a t N)
  have hz : (deltaDivisionFiniteRelationIdeal D d a N).map q = ⊥ :=
    (Ideal.map_eq_bot_iff_le_ker q).mpr hI
  simpa only [Ideal.map_sup, hz, bot_sup_eq, Ideal.map_span, Set.image_singleton] using h

/-- 下位関係を消す通常射の後、次段δ有限族の弱正則性は実評価有限族へ移る。 -/
theorem deltaDivisionMappedNextEvaluation_fin_isWeaklyRegular {m : ℕ} (s : Fin m → σ)
    (hr : RingTheory.Sequence.IsWeaklyRegular T (List.ofFn fun i =>
      q (deltaDivisionIteratedRelation D d a (s i) (N + 1)))) :
    RingTheory.Sequence.IsWeaklyRegular T (List.ofFn fun i =>
      q (deltaDivisionEvaluationRelation D d a (s i) (N + 1))) := by
  let f : σ → T := fun t => q (deltaDivisionEvaluationRelation D d a t (N + 1))
  let g : σ → T := fun t => q (deltaDivisionIteratedRelation D d a t (N + 1))
  have hspan (t : σ) : Ideal.span {f t} = Ideal.span {g t} :=
    deltaDivisionMappedNextEvaluation_span_eq D d a q N hI t
  have hList (l : List σ) : Ideal.ofList (l.map f) = Ideal.ofList (l.map g) := by
    induction l with
    | nil => rfl
    | cons t l ih => simp only [List.map_cons, Ideal.ofList_cons, hspan, ih]
  constructor
  intro i hi
  have hi' : i < m := by simpa only [List.length_ofFn] using hi
  have hw := hr.regular_mod_prev i (by simpa only [List.length_ofFn] using hi')
  have hprefix : Ideal.ofList ((List.ofFn fun j => f (s j)).take i) =
      Ideal.ofList ((List.ofFn fun j => g (s j)).take i) := by
    simpa only [List.map_take, List.map_ofFn, Function.comp_def] using
      hList ((List.ofFn s).take i)
  change IsSMulRegular (T ⧸
    (Ideal.ofList ((List.ofFn fun j => f (s j)).take i) • ⊤ : Submodule T T))
      ((List.ofFn fun j => f (s j))[i])
  rw [hprefix]
  simp only [List.getElem_ofFn] at hw ⊢
  have hm : g (s ⟨i, hi'⟩) ∈ Ideal.span {f (s ⟨i, hi'⟩)} :=
    (hspan _).symm ▸ Ideal.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hm
  intro x y hxy
  apply hw
  change g (s ⟨i, hi'⟩) • x = g (s ⟨i, hi'⟩) • y
  change f (s ⟨i, hi'⟩) • x = f (s ⟨i, hi'⟩) • y at hxy
  rw [hc, mul_comm, mul_smul, mul_smul, hxy]

/-- 同じ実評価有限族は、通常商のKoszul分解を与える。 -/
theorem deltaDivisionMappedNextEvaluation_fin_isKoszulResolution {m : ℕ} (s : Fin m → σ)
    (hr : RingTheory.Sequence.IsWeaklyRegular T (List.ofFn fun i =>
      q (deltaDivisionIteratedRelation D d a (s i) (N + 1)))) :
    SerrePositivity.IsKoszulResolution (fun i =>
      q (deltaDivisionEvaluationRelation D d a (s i) (N + 1))) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (deltaDivisionMappedNextEvaluation_fin_isWeaklyRegular D d a q N hI s hr)

end SerrePositivity.BhattScholze
