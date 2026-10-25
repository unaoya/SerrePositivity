module

public import SerrePositivity.BhattScholze.Prism.PCompletedDeltaDivisionSequential

/-! # 段階的除算添加の具体的なδ同型とmod d商同型

一意存在定理から具体的な同型を選び、標準基底射との両立を公開する。
導来(p,d)完備化との比較やperfectoid化の存在は仮定しない。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]
variable {σ : Type v} {τ : Type w}

/-- 一括添加から二段添加への、基底射と両立する具体的な環同型。 -/
def pCompletedDeltaDivisionSequentialEquiv
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R) :
    PCompletedDeltaDivision D d (Sum.elim a b) ≃+*
      SequentialPCompletedDeltaDivision D d a b :=
  (existsUnique_pCompletedDeltaDivisionSequentialEquiv D d hd a b).choose

/-- 一括添加から二段添加への同型はδ射。 -/
theorem pCompletedDeltaDivisionSequentialEquiv_isDeltaHom
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R) :
    (pCompletedDeltaDivisionStructure D d (Sum.elim a b)).IsDeltaHom
      (sequentialPCompletedDeltaDivisionStructure D d a b)
      (pCompletedDeltaDivisionSequentialEquiv D d hd a b).toRingHom :=
  (existsUnique_pCompletedDeltaDivisionSequentialEquiv D d hd a b).choose_spec.1.1

/-- 同型は元の環からの標準射と両立する。 -/
theorem pCompletedDeltaDivisionSequentialEquiv_comp_base
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R) :
    (pCompletedDeltaDivisionSequentialEquiv D d hd a b).toRingHom.comp
      (pCompletedDeltaDivisionMap D d (Sum.elim a b)) =
      sequentialPCompletedDeltaDivisionMap D d a b :=
  (existsUnique_pCompletedDeltaDivisionSequentialEquiv D d hd a b).choose_spec.1.2

/-- 二段添加から一括添加への逆同型もδ射。 -/
theorem pCompletedDeltaDivisionSequentialEquiv_symm_isDeltaHom
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R) :
    (sequentialPCompletedDeltaDivisionStructure D d a b).IsDeltaHom
      (pCompletedDeltaDivisionStructure D d (Sum.elim a b))
      (pCompletedDeltaDivisionSequentialEquiv D d hd a b).symm.toRingHom :=
  (pCompletedDeltaDivisionSequentialEquiv_isDeltaHom D d hd a b).symm

/-- 一括添加と二段添加のmod d商の具体的な環同型。 -/
def pCompletedDeltaDivisionSequentialQuotientEquiv
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R) :
    (PCompletedDeltaDivision D d (Sum.elim a b) ⧸
      Ideal.span {pCompletedDeltaDivisionMap D d (Sum.elim a b) d}) ≃+*
      (SequentialPCompletedDeltaDivision D d a b ⧸
        Ideal.span {sequentialPCompletedDeltaDivisionMap D d a b d}) :=
  Ideal.quotientEquiv _ _ (pCompletedDeltaDivisionSequentialEquiv D d hd a b) (by
    rw [Ideal.map_span, Set.image_singleton]
    congr 1
    exact congrArg (fun x ↦ ({x} : Set (SequentialPCompletedDeltaDivision D d a b)))
      (RingHom.congr_fun (pCompletedDeltaDivisionSequentialEquiv_comp_base D d hd a b) d).symm)

/-- 商同型は代表元に具体的なδ同型を適用する。 -/
@[simp] theorem pCompletedDeltaDivisionSequentialQuotientEquiv_mk
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R)
    (x : PCompletedDeltaDivision D d (Sum.elim a b)) :
    pCompletedDeltaDivisionSequentialQuotientEquiv D d hd a b (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (pCompletedDeltaDivisionSequentialEquiv D d hd a b x) := rfl

/-- mod d商同型も元の環からの標準射と両立する。 -/
theorem pCompletedDeltaDivisionSequentialQuotientEquiv_comp_base
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R) :
    (pCompletedDeltaDivisionSequentialQuotientEquiv D d hd a b).toRingHom.comp
      ((Ideal.Quotient.mk _).comp (pCompletedDeltaDivisionMap D d (Sum.elim a b))) =
      (Ideal.Quotient.mk _).comp (sequentialPCompletedDeltaDivisionMap D d a b) := by
  ext r
  change Ideal.Quotient.mk _ (pCompletedDeltaDivisionSequentialEquiv D d hd a b
    (pCompletedDeltaDivisionMap D d (Sum.elim a b) r)) =
      Ideal.Quotient.mk _ (sequentialPCompletedDeltaDivisionMap D d a b r)
  exact congrArg (Ideal.Quotient.mk _)
    (RingHom.congr_fun (pCompletedDeltaDivisionSequentialEquiv_comp_base D d hd a b) r)

end SerrePositivity.BhattScholze
