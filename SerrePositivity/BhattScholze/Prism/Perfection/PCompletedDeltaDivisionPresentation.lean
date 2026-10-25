module

public import SerrePositivity.BhattScholze.Prism.Perfection.PCompletedDeltaDivisionComparison
public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta

/-! # p進完備δ除算候補の生成元族からの独立性

任意の二つの元族が同じイデアルを生成すれば、候補の具体的なδ環同型とmod d商同型を得る。
有限生成性は要求しない。perfectoid性やIsPerfectoidizationとはまだ同定しない。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]
variable {σ : Type v} {τ : Type w}

/-- 同じイデアルを生成する任意の元族の標準比較射は全単射。 -/
theorem pCompletedDeltaDivisionComparisonMap_bijective_of_span_eq
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R)
    (hab : Ideal.span (Set.range a) = Ideal.span (Set.range b)) :
    Function.Bijective (pCompletedDeltaDivisionComparisonMap D d hd a b hab.le) := by
  let f := pCompletedDeltaDivisionComparisonMap D d hd a b hab.le
  let g := pCompletedDeltaDivisionComparisonMap D d hd b a hab.ge
  have hgf : g.comp f = RingHom.id (PCompletedDeltaDivision D d a) := by
    simpa only [pCompletedDeltaDivisionComparisonMap_id] using
      (pCompletedDeltaDivisionComparisonMap_comp D d hd a b a hab.le hab.ge).symm
  have hfg : f.comp g = RingHom.id (PCompletedDeltaDivision D d b) := by
    simpa only [pCompletedDeltaDivisionComparisonMap_id] using
      (pCompletedDeltaDivisionComparisonMap_comp D d hd b a b hab.ge hab.le).symm
  have hl : Function.LeftInverse g f := fun x ↦ RingHom.congr_fun hgf x
  have hr : Function.RightInverse g f := fun x ↦ RingHom.congr_fun hfg x
  exact ⟨hl.injective, hr.surjective⟩

/-- 同じイデアルを生成する二つの元族の候補環の具体的な標準同型。 -/
def pCompletedDeltaDivisionPresentationEquiv
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R)
    (hab : Ideal.span (Set.range a) = Ideal.span (Set.range b)) :
    PCompletedDeltaDivision D d a ≃+* PCompletedDeltaDivision D d b :=
  RingEquiv.ofBijective (pCompletedDeltaDivisionComparisonMap D d hd a b hab.le)
    (pCompletedDeltaDivisionComparisonMap_bijective_of_span_eq D d hd a b hab)

/-- 標準同型の台環射は生成イデアルの包含による標準比較射。 -/
@[simp] theorem pCompletedDeltaDivisionPresentationEquiv_toRingHom
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R)
    (hab : Ideal.span (Set.range a) = Ideal.span (Set.range b)) :
    (pCompletedDeltaDivisionPresentationEquiv D d hd a b hab).toRingHom =
      pCompletedDeltaDivisionComparisonMap D d hd a b hab.le := rfl

/-- 標準同型は元の基底射と可換。 -/
@[simp] theorem pCompletedDeltaDivisionPresentationEquiv_comp_base
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R)
    (hab : Ideal.span (Set.range a) = Ideal.span (Set.range b)) :
    (pCompletedDeltaDivisionPresentationEquiv D d hd a b hab).toRingHom.comp
      (pCompletedDeltaDivisionMap D d a) = pCompletedDeltaDivisionMap D d b :=
  pCompletedDeltaDivisionComparisonMap_comp_base D d hd a b hab.le

/-- 標準同型の逆もδ射。 -/
theorem pCompletedDeltaDivisionPresentationEquiv_symm_isDeltaHom
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R)
    (hab : Ideal.span (Set.range a) = Ideal.span (Set.range b)) :
    (pCompletedDeltaDivisionStructure D d b).IsDeltaHom (pCompletedDeltaDivisionStructure D d a)
      (pCompletedDeltaDivisionPresentationEquiv D d hd a b hab).symm.toRingHom :=
  DeltaStructure.IsDeltaHom.symm (pCompletedDeltaDivisionComparisonMap_isDeltaHom D d hd a b hab.le)

/-- 任意の生成元族の候補と、イデアルの全元を添加する候補との具体的な同型。
有限表示への変更は行わず、任意のイデアルJを保つ。 -/
def pCompletedDeltaDivisionIdealEquiv
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R)
    (J : Ideal R) (hJ : Ideal.span (Set.range a) = J) :
    PCompletedDeltaDivision D d a ≃+* PCompletedDeltaDivision D d (fun x : J ↦ (x : R)) :=
  pCompletedDeltaDivisionPresentationEquiv D d hd a (fun x : J ↦ (x : R))
    (hJ.trans (by
      have hr : Set.range (fun x : J ↦ (x : R)) = (J : Set R) := by
        ext r
        simp
      rw [hr, Ideal.span_eq]))

/-- 同じイデアルを生成する元族の候補のmod d商の具体的な同型。 -/
def pCompletedDeltaDivisionPresentationQuotientEquiv
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R)
    (hab : Ideal.span (Set.range a) = Ideal.span (Set.range b)) :
    (PCompletedDeltaDivision D d a ⧸ Ideal.span {pCompletedDeltaDivisionMap D d a d}) ≃+*
      (PCompletedDeltaDivision D d b ⧸ Ideal.span {pCompletedDeltaDivisionMap D d b d}) :=
  Ideal.quotientEquiv _ _ (pCompletedDeltaDivisionPresentationEquiv D d hd a b hab) (by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {pCompletedDeltaDivisionMap D d b d} =
      Ideal.span {(pCompletedDeltaDivisionComparisonMap D d hd a b hab.le
        (pCompletedDeltaDivisionMap D d a d))}
    rw [show pCompletedDeltaDivisionComparisonMap D d hd a b hab.le
      (pCompletedDeltaDivisionMap D d a d) = pCompletedDeltaDivisionMap D d b d from
        RingHom.congr_fun (pCompletedDeltaDivisionComparisonMap_comp_base D d hd a b hab.le) d])

/-- mod d商同型は代表元上で標準比較射を適用する。 -/
@[simp] theorem pCompletedDeltaDivisionPresentationQuotientEquiv_mk
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R)
    (hab : Ideal.span (Set.range a) = Ideal.span (Set.range b))
    (x : PCompletedDeltaDivision D d a) :
    pCompletedDeltaDivisionPresentationQuotientEquiv D d hd a b hab (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (pCompletedDeltaDivisionComparisonMap D d hd a b hab.le x) := rfl

/-- mod d商の比較同型も、元のRからの二つの標準射と可換する。 -/
theorem pCompletedDeltaDivisionPresentationQuotientEquiv_comp_base
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R)
    (hab : Ideal.span (Set.range a) = Ideal.span (Set.range b)) :
    (pCompletedDeltaDivisionPresentationQuotientEquiv D d hd a b hab).toRingHom.comp
      ((Ideal.Quotient.mk _).comp (pCompletedDeltaDivisionMap D d a)) =
        (Ideal.Quotient.mk _).comp (pCompletedDeltaDivisionMap D d b) := by
  apply RingHom.ext
  intro r
  simp only [RingHom.comp_apply]
  exact congrArg (Ideal.Quotient.mk _)
    (RingHom.congr_fun (pCompletedDeltaDivisionComparisonMap_comp_base D d hd a b hab.le) r)

end SerrePositivity.BhattScholze
