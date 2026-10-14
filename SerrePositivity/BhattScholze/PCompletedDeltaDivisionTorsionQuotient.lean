module

public import SerrePositivity.BhattScholze.PCompletedDeltaDivisionTorsion
public import SerrePositivity.BhattScholze.PCompletedDeltaDivisionQuotient
public import SerrePositivity.BhattScholze.DeltaDivisionQuotient

/-! # 旧ねじれ除去前後の候補のmod d商と標準射の比較

具体的なp進完備δ完全化の比較同型をmod d商へ誘導し、R/Jからの標準射を比較する。
perfectoid性・IsPerfectoidization・原典の導来(p,d)完備化との同定は未結論。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {σ : Type v}

/-- 旧ねじれ除去前後の候補環のmod d商を比較する具体的な同型。 -/
def pCompletedDeltaDivisionTorsionQuotientEquiv
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) :
    (PCompletedDeltaDivision D d a ⧸ Ideal.span {pCompletedDeltaDivisionMap D d a d}) ≃+*
      (PCompletedDeltaPerfection (deltaDivisionTorsionStructure D d a) ⧸
        Ideal.span {(pCompletedDeltaPerfectionMap (deltaDivisionTorsionStructure D d a)
          (deltaDivisionTorsionMap D d a d))}) :=
  Ideal.quotientEquiv _ _ (pCompletedDeltaDivisionTorsionEquiv D d hd a) (by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {(pCompletedDeltaPerfectionMap (deltaDivisionTorsionStructure D d a)
      (deltaDivisionTorsionMap D d a d))} =
      Ideal.span {pCompletedDeltaDivisionTorsionMap D d a (pCompletedDeltaDivisionMap D d a d)}
    rw [show pCompletedDeltaDivisionTorsionMap D d a (pCompletedDeltaDivisionMap D d a d) =
      pCompletedDeltaPerfectionMap (deltaDivisionTorsionStructure D d a)
        (deltaDivisionTorsionMap D d a d) from
          RingHom.congr_fun (pCompletedDeltaDivisionTorsionMap_comp_base D d a) d])

/-- mod d比較同型は、代表元へ標準比較射を適用する。 -/
@[simp] theorem pCompletedDeltaDivisionTorsionQuotientEquiv_mk
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R)
    (x : PCompletedDeltaDivision D d a) :
    pCompletedDeltaDivisionTorsionQuotientEquiv D d hd a (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (pCompletedDeltaDivisionTorsionMap D d a x) := rfl

/-- 旧ねじれ除去商のmod dから、そのp進完備δ完全化のmod dへの標準誘導射。 -/
def deltaDivisionTorsionToCompletedQuotientMap
    (D : DeltaStructure p R) (d : R) (a : σ → R) :
    (DeltaDivisionTorsionQuotient D d a ⧸ Ideal.span {deltaDivisionTorsionMap D d a d}) →+*
      (PCompletedDeltaPerfection (deltaDivisionTorsionStructure D d a) ⧸
        Ideal.span {(pCompletedDeltaPerfectionMap (deltaDivisionTorsionStructure D d a)
          (deltaDivisionTorsionMap D d a d))}) :=
  Ideal.quotientMap _ (pCompletedDeltaPerfectionMap (deltaDivisionTorsionStructure D d a)) (by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    exact Ideal.subset_span (Set.mem_singleton _))

/-- 旧ねじれ除去商の標準誘導射は、代表元に完全化の標準射を適用する。 -/
@[simp] theorem deltaDivisionTorsionToCompletedQuotientMap_mk
    (D : DeltaStructure p R) (d : R) (a : σ → R) (x : DeltaDivisionTorsionQuotient D d a) :
    deltaDivisionTorsionToCompletedQuotientMap D d a (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _
        (pCompletedDeltaPerfectionMap (deltaDivisionTorsionStructure D d a) x) := rfl

/-- 任意のR/Jからの二つの標準射は、上の具体的なmod d比較同型で一致する。 -/
theorem pCompletedDeltaDivisionTorsionQuotientEquiv_comp_base
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (J : Ideal R) :
    (pCompletedDeltaDivisionTorsionQuotientEquiv D d hd (fun x : J ↦ (x : R))).toRingHom.comp
      (pCompletedDeltaDivisionQuotientMap D d J) =
        (deltaDivisionTorsionToCompletedQuotientMap D d (fun x : J ↦ (x : R))).comp
          (deltaDivisionQuotientMap D d J) := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro r
  simp only [RingHom.comp_apply, pCompletedDeltaDivisionQuotientMap_mk,
    deltaDivisionQuotientMap_mk, deltaDivisionTorsionToCompletedQuotientMap_mk]
  exact congrArg (Ideal.Quotient.mk _)
    (RingHom.congr_fun (pCompletedDeltaDivisionTorsionMap_comp_base D d (fun x : J ↦ (x : R))) r)

end SerrePositivity.BhattScholze
