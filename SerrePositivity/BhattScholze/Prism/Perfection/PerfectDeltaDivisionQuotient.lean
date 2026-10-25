module

public import SerrePositivity.BhattScholze.Prism.Perfection.PerfectDeltaDivisionPrism

/-! # 任意の基底商から完全prism候補の標準商への射

具体的なR/Jの射と標準商の古典的p完備性を公開する。
候補商のperfectoid性・IsPerfectoidizationは別工程。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- Jの全元の像は、候補prismのイデアルへ入る。 -/
theorem perfectDeltaDivisionPrismMap_ideal_le
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (J : Ideal R) :
    letI := perfectDeltaDivisionPrismCommRing D d J
    J ≤ (perfectDeltaDivisionPrism D d hd J).ideal.comap (perfectDeltaDivisionPrismMap D d J) := by
  let := perfectDeltaDivisionPrismCommRing D d J
  intro x hx
  apply Ideal.mem_span_singleton.mpr
  change pdCompletionUnit _ p _ (pCompletedDeltaDivisionMap D d (fun y : J ↦ (y : R)) d) ∣
    pdCompletionUnit _ p _ (pCompletedDeltaDivisionMap D d (fun y : J ↦ (y : R)) x)
  exact map_dvd (pdCompletionUnit _ p _)
    (pCompletedDeltaDivisionMap_dvd D d (fun y : J ↦ (y : R)) ⟨x, hx⟩)

/-- 任意の基底商R/Jから候補prismの標準商への具体的な射。 -/
def perfectDeltaDivisionQuotientMap
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (J : Ideal R) :
    letI := perfectDeltaDivisionPrismCommRing D d J
    R ⧸ J →+* PerfectDeltaDivisionPrismCarrier D d J ⧸
      (perfectDeltaDivisionPrism D d hd J).ideal := by
  letI := perfectDeltaDivisionPrismCommRing D d J
  exact Ideal.quotientMap _ (perfectDeltaDivisionPrismMap D d J)
    (perfectDeltaDivisionPrismMap_ideal_le D d hd J)

/-- 標準商射の代表元公式。 -/
@[simp] theorem perfectDeltaDivisionQuotientMap_mk
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (J : Ideal R) (x : R) :
    letI := perfectDeltaDivisionPrismCommRing D d J
    perfectDeltaDivisionQuotientMap D d hd J (Ideal.Quotient.mk J x) =
      Ideal.Quotient.mk _ (perfectDeltaDivisionPrismMap D d J x) := rfl

/-- 候補prismの標準商は、pねじれを許して古典的p進完備。 -/
theorem perfectDeltaDivisionQuotient_isAdicComplete
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (J : Ideal R) :
    letI := perfectDeltaDivisionPrismCommRing D d J
    IsAdicComplete (Ideal.span {(p : PerfectDeltaDivisionPrismCarrier D d J ⧸
      (perfectDeltaDivisionPrism D d hd J).ideal)})
      (PerfectDeltaDivisionPrismCarrier D d J ⧸ (perfectDeltaDivisionPrism D d hd J).ideal) := by
  let := perfectDeltaDivisionPrismCommRing D d J
  let P := perfectDeltaDivisionPrism D d hd J
  have hP := perfectDeltaDivisionPrism_isPerfect D d hd J
  let := P.isAdicComplete_p_of_perfect hP
  exact hP.distinguished_quotient_isAdicComplete (P.isDistinguished_of_perfect hP)

end SerrePositivity.BhattScholze
