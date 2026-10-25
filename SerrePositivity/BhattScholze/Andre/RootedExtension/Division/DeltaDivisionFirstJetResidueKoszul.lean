module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Division.DeltaDivisionFirstJetResidueRegular
public import SerrePositivity.BhattScholze.Andre.RootedExtension.DeltaRoot.DeltaRootFiniteRegularSequence

/-! # 最初のδ関係の有限族のmod(p,d)Koszul分解

全深さ0を課した実mod(p,d)商上で、異なる有限個の深さ1関係を同時に扱う。
添字環の一元性・有限性やghost単射・完備性は要求しない。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze

private theorem unit_mul_list_regular {R : Type u} [CommRing R] (w : Rˣ) (l : List R)
    (h : RingTheory.Sequence.IsWeaklyRegular R l) :
    RingTheory.Sequence.IsWeaklyRegular R (l.map fun x => (w : R) * x) := by
  have hI (t : List R) : Ideal.ofList (t.map fun x => (w : R) * x) = Ideal.ofList t := by
    induction t with
    | nil => rfl
    | cons x t ih =>
        simp only [List.map_cons, Ideal.ofList_cons, ih,
          Ideal.span_singleton_mul_left_unit w.isUnit]
  constructor
  intro i hi
  have hi' : i < l.length := by simpa only [List.length_map] using hi
  rw [← List.map_take, hI, List.getElem_map]
  exact (w.isSMulRegular _).mul (h.regular_mod_prev i hi')

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (v : Aˣ)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "J₀" => Ideal.span {(p : L₀), MvPolynomial.C d} ⊔
  deltaDivisionFiniteRelationIdeal D d a 0
local notation "K₀" => deltaDivisionFirstBaseIdeal (p := p) d a
local notation "f₀" => fun s : σ =>
  Ideal.Quotient.mk J₀ (deltaDivisionIteratedRelation D d a s 1)

/-- 指定単元δdに対し、異なる有限個の深さ1関係は実初期mod(p,d)商上で弱正則。 -/
theorem deltaDivisionFirstJetResidue_fin_isWeaklyRegular (hv : (v : A) = D.delta d)
    {m : ℕ} (s : Fin m → σ) (hs : Function.Injective s) :
    RingTheory.Sequence.IsWeaklyRegular (L₀ ⧸ J₀) (List.ofFn fun i => f₀ (s i)) := by
  let Q := A ⧸ K₀
  let w₀ := v.map (Ideal.Quotient.mk K₀).toMonoidHom
  let w := w₀.map (MvPolynomial.C : Q →+* MvPolynomial (σ × ℕ) Q).toMonoidHom
  let c : σ × ℕ → Q := fun z => ((w₀⁻¹ : Qˣ) : Q) *
    Ideal.Quotient.mk K₀ (D.delta (a z.1))
  let e := deltaDivisionInitialResiduePolynomialEquiv D d a
  have hr := deltaRootRelation_fin_isWeaklyRegular (p := p) c
    (fun i => (s i, 0)) (fun _ _ hij => hs (congrArg Prod.fst hij))
  have hm := unit_mul_list_regular w _ hr
  have he (t : σ) : e (f₀ t) = (w : MvPolynomial (σ × ℕ) Q) *
      deltaRootRelationFamily (p := p) c (t, 0) := by
    exact deltaDivisionFirstJet_residue_polynomial D d a v hv t
  have hc := e.toAddEquiv.isWeaklyRegular_congr
    (as := List.ofFn fun i => f₀ (s i))
    (bs := (List.ofFn fun i => f₀ (s i)).map e)
    (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr (fun r _ x => by
      change e (r * x) = e r * e x
      exact map_mul e r x)))
  apply hc.mpr
  simpa only [List.map_ofFn, Function.comp_def, he] using hm

/-- 最初のδ関係の異なる有限族のKoszul複体は、実初期mod(p,d)商上の実通常商の分解。 -/
theorem deltaDivisionFirstJetResidue_fin_isKoszulResolution (hv : (v : A) = D.delta d)
    {m : ℕ} (s : Fin m → σ) (hs : Function.Injective s) :
    SerrePositivity.IsKoszulResolution (fun i => f₀ (s i)) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (deltaDivisionFirstJetResidue_fin_isWeaklyRegular D d a v hv s hs)

end SerrePositivity.BhattScholze
