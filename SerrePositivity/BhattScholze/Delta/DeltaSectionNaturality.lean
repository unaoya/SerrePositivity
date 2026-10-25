module

public import SerrePositivity.BhattScholze.Delta.WittTwoMap

/-! # δ射とW₂切断の自然性

δ射の条件をW₂切断の可換図式として表す。自由δ環からの写像を
多項式環の普遍性で構成する際、pねじれのある終域も扱う。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- 環準同型がδ射であることと、W₂切断の図式が可換であることは同値。
二つのWitt座標で比較し、p正則性は要求しない（BS Remark 2.4）。 -/
theorem isDeltaHom_iff_sectionHom_comp (D : DeltaStructure p A) (E : DeltaStructure p B)
    (f : A →+* B) : D.IsDeltaHom E f ↔
      (wittTwoMap (p := p) f).comp D.sectionHom = E.sectionHom.comp f := by
  constructor
  · intro hf
    apply RingHom.ext
    intro x
    apply TruncatedWittVector.ext
    intro i
    fin_cases i
    · simp only [RingHom.comp_apply, wittTwoMap_coeff]
      change f ((D.sectionHom x).coeff 0) = (E.sectionHom (f x)).coeff 0
      rw [D.coeff_zero, E.coeff_zero]
    · simp only [RingHom.comp_apply, wittTwoMap_coeff]
      exact hf x
  · intro h x
    have hx := congrArg (fun z : WittTwo p B ↦ z.coeff 1) (DFunLike.congr_fun h x)
    simp only [RingHom.comp_apply, wittTwoMap_coeff] at hx
    exact hx

end SerrePositivity.BhattScholze.DeltaStructure
