module
public import SerrePositivity.DifferentialGraded.Quotient.HomogeneousNaturality
public import SerrePositivity.DifferentialGraded.Quotient.Extension

/-!
概要：選択された収縮と整合する全パラメータ変換を、同じ実商へ厳密に延長する。
方針：元 Hom の自然性と指定 ε の自然性から、全 path の全次数自然性を導く。
規約：収縮との整合はここでは明示する。D-8 e の実選択での充足は別途構成する。
使われ方：模型を変えず、同じ四角形の商辺・零角辺を全 native Hom 上で動かす部品。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex
variable (R : Type u) [CommRing R] {D : Type v} [DGCategory R D] [Small.{u} D]
  {S : Set D} {E : Type w} [DGCategory R E]
  (C C' : ContractedFunctor R D S E) {K : Complex R}
  (τ : GradedNatTrans ((Center.ofBraided (Complex R)).obj K) C.toDGFunctor C'.toDGFunctor)

def parameterExtension
    (hε : ∀ (b : S) (k : ℤ) (t : K.X k),
      forward R (C.homotopy b) ((τ.app b.val).f k t) rfl =
        (k * (-1)).negOnePow • forward R ((τ.app b.val).f k t) (C'.homotopy b) (by omega)) :
    GradedNatTrans ((Center.ofBraided (Complex R)).obj K) (extension R C) (extension R C') where
  app x := τ.app x.val
  naturality x y := by
    apply (gradedFamilyNaturality_iff_homogeneous R (extension R C) (extension R C')
      (fun z => τ.app z.val) x y).2
    intro k p t f
    apply homogeneousNaturality_of_generators R D S (extension R C) (extension R C')
      (fun z => (τ.app z.val).f k t) _ _ x y p f
    · intro a b q g
      have h := (gradedFamilyNaturality_iff_homogeneous R C.toDGFunctor C'.toDGFunctor
        τ.app a b).1 (τ.naturality a b) k q t g
      have hc := congrArg (fun m => m.f q g) (quotientEvaluation_original R C a b)
      have hc' := congrArg (fun m => m.f q g) (quotientEvaluation_original R C' a b)
      change (quotientEvaluation R C a b).f q ((originalHomInclusion R D S a b).f q g) =
        (C.toDGFunctor.map a b).f q g at hc
      change (quotientEvaluation R C' a b).f q ((originalHomInclusion R D S a b).f q g) =
        (C'.toDGFunctor.map a b).f q g at hc'
      change forward R ((quotientEvaluation R C a b).f q
        ((originalHomInclusion R D S a b).f q g)) ((τ.app b).f k t) rfl =
          (k * q).negOnePow • forward R ((τ.app a).f k t)
            ((quotientEvaluation R C' a b).f q
              ((originalHomInclusion R D S a b).f q g)) (by omega)
      rw [hc, hc']
      exact h
    · intro b
      change forward R ((quotientEvaluation R C b.val b.val).f (-1)
        (epsilonElement R D S b)) ((τ.app b.val).f k t) rfl =
          (k * (-1)).negOnePow • forward R ((τ.app b.val).f k t)
            ((quotientEvaluation R C' b.val b.val).f (-1) (epsilonElement R D S b)) (by omega)
      rw [quotientEvaluation_epsilon, quotientEvaluation_epsilon]
      exact hε b k t

lemma parameterExtension_app
    (hε : ∀ (b : S) (k : ℤ) (t : K.X k),
      forward R (C.homotopy b) ((τ.app b.val).f k t) rfl =
        (k * (-1)).negOnePow • forward R ((τ.app b.val).f k t) (C'.homotopy b) (by omega))
    (x : D) : (parameterExtension R C C' τ hε).app ⟨x⟩ = τ.app x := rfl

lemma parameterExtension_epsilon_necessary
    (σ : GradedNatTrans ((Center.ofBraided (Complex R)).obj K) (extension R C) (extension R C'))
    (hσ : ∀ x : D, σ.app ⟨x⟩ = τ.app x)
    (b : S) (k : ℤ) (t : K.X k) :
    forward R (C.homotopy b) ((τ.app b.val).f k t) rfl =
      (k * (-1)).negOnePow • forward R ((τ.app b.val).f k t) (C'.homotopy b) (by omega) := by
  have h := (gradedFamilyNaturality_iff_homogeneous R (extension R C) (extension R C')
    σ.app ⟨b.val⟩ ⟨b.val⟩).1 (σ.naturality ⟨b.val⟩ ⟨b.val⟩)
      k (-1) t (epsilonElement R D S b)
  change forward R ((quotientEvaluation R C b.val b.val).f (-1) (epsilonElement R D S b))
    ((σ.app ⟨b.val⟩).f k t) rfl =
      (k * (-1)).negOnePow • forward R ((σ.app ⟨b.val⟩).f k t)
        ((quotientEvaluation R C' b.val b.val).f (-1) (epsilonElement R D S b)) (by omega) at h
  rw [hσ b.val, quotientEvaluation_epsilon, quotientEvaluation_epsilon] at h
  exact h

/-- 同じ成分を保持する商上の全パラメータ延長の、正確な必要十分条件。 -/
theorem parameterExtension_exists_iff :
    (∃ σ : GradedNatTrans ((Center.ofBraided (Complex R)).obj K)
        (extension R C) (extension R C'), ∀ x : D, σ.app ⟨x⟩ = τ.app x) ↔
      ∀ (b : S) (k : ℤ) (t : K.X k),
        forward R (C.homotopy b) ((τ.app b.val).f k t) rfl =
          (k * (-1)).negOnePow • forward R ((τ.app b.val).f k t) (C'.homotopy b) (by omega) := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact parameterExtension_epsilon_necessary R C C' τ σ hσ
  · intro hε
    exact ⟨parameterExtension R C C' τ hε, fun _ => rfl⟩

theorem parameterExtension_unique
    (σ σ' : GradedNatTrans ((Center.ofBraided (Complex R)).obj K) (extension R C) (extension R C'))
    (h : ∀ x : D, σ.app ⟨x⟩ = σ'.app ⟨x⟩) : σ = σ' := by
  apply GradedNatTrans.ext
  funext x
  rcases x with ⟨x⟩
  exact h x

/-- 任意のパラメータ射で制限しても、同じ延長を厳密に回収する。 -/
theorem parameterExtension_reindex
    (hε : ∀ (b : S) (k : ℤ) (t : K.X k),
      forward R (C.homotopy b) ((τ.app b.val).f k t) rfl =
        (k * (-1)).negOnePow • forward R ((τ.app b.val).f k t) (C'.homotopy b) (by omega))
    {L : Complex R} (f : L ⟶ K) :
    parameterExtension R C C'
        ((enrichedNatTransYoneda C.toDGFunctor C'.toDGFunctor).map f.op τ)
        (fun b k t => hε b k (f.f k t)) =
      (enrichedNatTransYoneda (extension R C) (extension R C')).map f.op
        (parameterExtension R C C' τ hε) := by
  apply parameterExtension_unique R C C'
  intro x
  rfl

end SerrePositivity.DifferentialGraded.DGQuotient
