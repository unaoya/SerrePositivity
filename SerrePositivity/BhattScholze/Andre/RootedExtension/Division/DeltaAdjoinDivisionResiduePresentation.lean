module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Division.DeltaDivisionNormalizedDirectLimitFaithfullyFlat

/-! # 既存δ除算添加環のraw (p,d)商の具体的表示 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A)

/-- raw δ除算添加環における(p,基底dの像)の通常イデアル。 -/
def deltaAdjoinDivisionResidueIdeal : Ideal (DeltaAdjoinDivision D d a) :=
  Ideal.span {(p : DeltaAdjoinDivision D d a), deltaAdjoinDivisionMap D d a d}

/-- raw除算添加環の(p,d)商。ねじれ除去後のadic idealとは別の段階。 -/
abbrev DeltaAdjoinDivisionResidue :=
  DeltaAdjoinDivision D d a ⧸ deltaAdjoinDivisionResidueIdeal D d a

/-- raw環の残余イデアルは、無限自由環の(p,Cd)の標準商射による像。 -/
theorem deltaAdjoinDivisionResidueIdeal_eq_map :
    deltaAdjoinDivisionResidueIdeal D d a =
      Ideal.map (Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure
        (deltaDivisionRelationIdeal d a)))
        (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d}) := by
  rw [Ideal.map_span]
  simp only [Set.image_pair, map_natCast]
  rfl

/-- raw添加環の(p,d)商は、無限自由環で(p,Cd)とδ閉包を同時に課した商。 -/
def deltaAdjoinDivisionResidueSupEquiv :
    DeltaAdjoinDivisionResidue D d a ≃+*
      (RelativeFreeDeltaRing (R := A) σ ⧸
        (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
          (relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a))) :=
  (Ideal.quotEquivOfEq (deltaAdjoinDivisionResidueIdeal_eq_map D d a)).trans
    ((DoubleQuot.quotQuotEquivQuotSup
      ((relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a))
      (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d})).trans
      (Ideal.quotEquivOfEq (sup_comm _ _)))

/-- 二重商表示同型は元の無限自由環の標準像を同時商の標準像に送る。 -/
theorem deltaAdjoinDivisionResidueSupEquiv_mk (f : RelativeFreeDeltaRing (R := A) σ) :
    deltaAdjoinDivisionResidueSupEquiv D d a
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ f)) = Ideal.Quotient.mk _ f := by
  rw [deltaAdjoinDivisionResidueSupEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingEquiv.trans_apply]
  change (Ideal.quotEquivOfEq (sup_comm _ _))
    (DoubleQuot.quotQuotEquivQuotSup
      ((relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a))
      (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d})
      (DoubleQuot.quotQuotMk
        ((relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a))
        (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d}) f)) = _
  rw [DoubleQuot.quotQuotEquivQuotSup_quotQuotMk, Ideal.quotEquivOfEq_mk]

/-- 基底係数上での二重商比較の標準写像図式。 -/
theorem deltaAdjoinDivisionResidueSupEquiv_coeff (b : A) :
    deltaAdjoinDivisionResidueSupEquiv D d a
      (Ideal.Quotient.mk _ (deltaAdjoinDivisionMap D d a b)) =
      Ideal.Quotient.mk _ (MvPolynomial.C b) :=
  deltaAdjoinDivisionResidueSupEquiv_mk D d a (MvPolynomial.C b)

end SerrePositivity.BhattScholze
