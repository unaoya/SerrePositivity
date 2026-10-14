module

public import SerrePositivity.BhattScholze.RelativeFreeDelta
public import Mathlib.Logic.Function.Iterate

/-! # 相対自由δ環の普遍性

任意の基底δ射と生成元像の指定から、基底と両立する一意なδ射を構成する。
基底・終域のpねじれを許す。BS著者版Notation 2.8のδ元の添加に用いる。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]
    {σ : Type v} {A : Type w} [CommRing A]

/-- 基底射fと元族a_sから、各x_(s,n)をδ^n(a_s)へ評価する環準同型。 -/
def relativeFreeDeltaEval (E : DeltaStructure p A) (f : R →+* A) (a : σ → A) :
    RelativeFreeDeltaRing (R := R) σ →+* A :=
  MvPolynomial.eval₂Hom f (fun v ↦ E.delta^[v.2] (a v.1))

/-- 相対評価射は係数上で基底射fに一致する。 -/
@[simp] theorem relativeFreeDeltaEval_C (E : DeltaStructure p A) (f : R →+* A)
    (a : σ → A) (r : R) : relativeFreeDeltaEval E f a (MvPolynomial.C r) = f r := by
  simp [relativeFreeDeltaEval]

/-- 相対評価射の生成元上の値。 -/
@[simp] theorem relativeFreeDeltaEval_X (E : DeltaStructure p A) (f : R →+* A)
    (a : σ → A) (s : σ) (n : ℕ) :
    relativeFreeDeltaEval E f a (MvPolynomial.X (s, n)) = E.delta^[n] (a s) := by
  simp [relativeFreeDeltaEval]

/-- 基底射がδ射なら相対評価射もδ射。W₂切断の自然性を係数・変数の二座標で確認する。 -/
theorem relativeFreeDeltaEval_isDeltaHom (D : DeltaStructure p R) (E : DeltaStructure p A)
    (f : R →+* A) (hf : D.IsDeltaHom E f) (a : σ → A) :
    (relativeFreeDeltaStructure σ D).IsDeltaHom E (relativeFreeDeltaEval E f a) := by
  apply (DeltaStructure.isDeltaHom_iff_sectionHom_comp _ _ _).mpr
  apply MvPolynomial.ringHom_ext
  · intro r
    apply TruncatedWittVector.ext
    intro i
    fin_cases i
    · simp only [RingHom.comp_apply, wittTwoMap_coeff]
      change relativeFreeDeltaEval E f a
        (((relativeFreeDeltaStructure σ D).sectionHom (MvPolynomial.C r)).coeff 0) =
          (E.sectionHom (relativeFreeDeltaEval E f a (MvPolynomial.C r))).coeff 0
      rw [DeltaStructure.coeff_zero, E.coeff_zero]
    · simp only [RingHom.comp_apply, wittTwoMap_coeff]
      change relativeFreeDeltaEval E f a ((relativeFreeDeltaStructure σ D).delta
        (MvPolynomial.C r)) = E.delta (relativeFreeDeltaEval E f a (MvPolynomial.C r))
      rw [relativeFreeDeltaStructure_delta_C, relativeFreeDeltaEval_C,
        relativeFreeDeltaEval_C, hf r]
  · rintro ⟨s, n⟩
    apply TruncatedWittVector.ext
    intro i
    fin_cases i
    · simp only [RingHom.comp_apply, wittTwoMap_coeff]
      change relativeFreeDeltaEval E f a
        (((relativeFreeDeltaStructure σ D).sectionHom (MvPolynomial.X (s, n))).coeff 0) =
          (E.sectionHom (relativeFreeDeltaEval E f a (MvPolynomial.X (s, n)))).coeff 0
      rw [DeltaStructure.coeff_zero, E.coeff_zero]
    · simp only [RingHom.comp_apply, wittTwoMap_coeff]
      change relativeFreeDeltaEval E f a ((relativeFreeDeltaStructure σ D).delta
        (MvPolynomial.X (s, n))) = E.delta (relativeFreeDeltaEval E f a (MvPolynomial.X (s, n)))
      rw [relativeFreeDeltaStructure_delta_X, relativeFreeDeltaEval_X,
        relativeFreeDeltaEval_X, Function.iterate_succ_apply']

/-- 相対自由δ環からのδ射では、全座標の像が初期座標の像から決まる。 -/
theorem relativeFreeDeltaHom_X_iterates (D : DeltaStructure p R) (E : DeltaStructure p A)
    (g : RelativeFreeDeltaRing (R := R) σ →+* A)
    (hg : (relativeFreeDeltaStructure σ D).IsDeltaHom E g) (s : σ) (n : ℕ) :
    g (MvPolynomial.X (s, n)) = E.delta^[n] (g (MvPolynomial.X (s, 0))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [← relativeFreeDeltaStructure_delta_X σ D s n, hg, ih, Function.iterate_succ_apply']

/-- 任意の基底δ射f:R→Aと元族a_sに対し、基底上f、初期生成元上a_sとなるδ射が一意に存在。
基底射との両立条件を具体的な環準同型の等式で述べ、完備性・p正則性を要求しない。 -/
theorem existsUnique_relativeFreeDeltaHom (D : DeltaStructure p R) (E : DeltaStructure p A)
    (f : R →+* A) (hf : D.IsDeltaHom E f) (a : σ → A) :
    ∃! g : RelativeFreeDeltaRing (R := R) σ →+* A,
      (relativeFreeDeltaStructure σ D).IsDeltaHom E g ∧
        g.comp MvPolynomial.C = f ∧ ∀ s : σ, g (MvPolynomial.X (s, 0)) = a s := by
  have hC : (relativeFreeDeltaEval E f a).comp MvPolynomial.C = f := by
    ext r
    simp
  refine ⟨relativeFreeDeltaEval E f a,
    ⟨relativeFreeDeltaEval_isDeltaHom D E f hf a, hC, ?_⟩, ?_⟩
  · intro s
    simp
  · intro g hg
    apply MvPolynomial.ringHom_ext' (hg.2.1.trans hC.symm)
    rintro ⟨s, n⟩
    rw [relativeFreeDeltaHom_X_iterates D E g hg.1 s n, hg.2.2 s, relativeFreeDeltaEval_X]

end SerrePositivity.BhattScholze
