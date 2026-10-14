module

public import SerrePositivity.BhattScholze.DeltaRootAdjoinCompatibleRoots
public import SerrePositivity.BhattScholze.PCompletedDeltaDivision
public import SerrePositivity.BhattScholze.PerfectDeltaPDPrism
public import SerrePositivity.BhattScholze.PerfectPrismQuotientPerfectoid

/-! # 根δ除算包からの具体的なperfectoid候補

既存のp進完備δ完全化と実PD完備化を使用する。標準基底射の完全忠実平坦性は
この構成からは結論しない。商のpねじれ・零環を許す。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (b : σ → A)

/-- 根δ除算包の既存p進完備δ完全化。 -/
abbrev DeltaRootPCompletion :=
  PCompletedDeltaDivision (polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
    (deltaRootRelationFamily (p := p) b)

/-- p進完備δ完全化における選択元dの標準像。 -/
def deltaRootPCompletionGenerator : DeltaRootPCompletion D d b :=
  pCompletedDeltaDivisionMap (polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
    (deltaRootRelationFamily (p := p) b) (MvPolynomial.C d)

/-- 根候補の実導来(p,d)完備化のH⁰。 -/
abbrev DeltaRootPrismCarrier :=
  PDCompletionH0 (DeltaRootPCompletion D d b) p (deltaRootPCompletionGenerator D d b)

/-- 実完備化に既存の可換環構造を使用する。 -/
@[instance_reducible] def deltaRootPrismCommRing : CommRing (DeltaRootPrismCarrier D d b) :=
  pdCompletionCommRing (DeltaRootPCompletion D d b) p (deltaRootPCompletionGenerator D d b)

/-- distinguished dを持つ基底からの具体的な完全prism候補。 -/
def deltaRootPrism (hd : D.IsDistinguished d) :
    letI := deltaRootPrismCommRing D d b
    OrientedPrism p (DeltaRootPrismCarrier D d b) := by
  let := deltaRootPrismCommRing D d b
  exact perfectDeltaPDPrism
    (pCompletedDeltaDivisionStructure (polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
      (deltaRootRelationFamily (p := p) b))
    (pCompletedDeltaDivision_isPerfect _ _ _) (deltaRootPCompletionGenerator D d b)
    ((pCompletedDeltaDivisionMap_isDeltaHom _ _ _).map_isDistinguished
      ((polynomialRankOneDeltaStructure_C_isDeltaHom σ D).map_isDistinguished hd))

/-- 候補prismのδ構造は完全。 -/
theorem deltaRootPrism_isPerfect (hd : D.IsDistinguished d) :
    letI := deltaRootPrismCommRing D d b
    (deltaRootPrism D d b hd).deltaStructure.IsPerfect := by
  let := deltaRootPrismCommRing D d b
  exact deltaPDCompletionStructure_isPerfect
    (pCompletedDeltaDivisionStructure (polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
      (deltaRootRelationFamily (p := p) b))
    (pCompletedDeltaDivision_isPerfect _ _ _) (deltaRootPCompletionGenerator D d b)

/-- raw根δ除算包から実完備化への標準射。 -/
def deltaRootPrismRawMap :
    letI := deltaRootPrismCommRing D d b
    DeltaRootAdjoinDivision D d b →+* DeltaRootPrismCarrier D d b :=
  (pdCompletionUnit (DeltaRootPCompletion D d b) p (deltaRootPCompletionGenerator D d b)).comp
    (pCompletedDeltaPerfectionMap (deltaAdjoinDivisionStructure
      (polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
      (deltaRootRelationFamily (p := p) b)))

/-- 標準raw射は既存の二つのδ射の合成。 -/
theorem deltaRootPrismRawMap_isDeltaHom (hd : D.IsDistinguished d) :
    letI := deltaRootPrismCommRing D d b
    (deltaAdjoinDivisionStructure (polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
      (deltaRootRelationFamily (p := p) b)).IsDeltaHom
      (deltaRootPrism D d b hd).deltaStructure (deltaRootPrismRawMap D d b) := by
  let := deltaRootPrismCommRing D d b
  exact (pdCompletionUnit_isDeltaHom _ _).comp (pCompletedDeltaPerfectionMap_isDeltaHom _)

/-- 完全prism候補の標準商を実際のperfectoid候補とする。 -/
abbrev DeltaRootPerfectoidCandidate (hd : D.IsDistinguished d) :=
  letI := deltaRootPrismCommRing D d b
  DeltaRootPrismCarrier D d b ⧸ (deltaRootPrism D d b hd).ideal

/-- 候補の標準商は整perfectoid。標準基底射の平坦性は別の主張。 -/
theorem deltaRootPerfectoidCandidate_isIntegralPerfectoid (hd : D.IsDistinguished d) :
    letI := deltaRootPrismCommRing D d b
    IsIntegralPerfectoid (DeltaRootPerfectoidCandidate D d b hd) p := by
  let := deltaRootPrismCommRing D d b
  exact (deltaRootPrism D d b hd).quotient_isIntegralPerfectoid
    (deltaRootPrism_isPerfect D d b hd)

/-- 基底δ環から候補の通常商への具体的係数射。 -/
def deltaRootPerfectoidCandidateCoefficientMap (hd : D.IsDistinguished d) :
    letI := deltaRootPrismCommRing D d b
    A →+* DeltaRootPerfectoidCandidate D d b hd := by
  let := deltaRootPrismCommRing D d b
  exact (Ideal.Quotient.mk (deltaRootPrism D d b hd).ideal).comp
    ((deltaRootPrismRawMap D d b).comp
      ((deltaAdjoinDivisionMap (polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
        (deltaRootRelationFamily (p := p) b)).comp MvPolynomial.C))

/-- 選択元dの係数像は標準商で零になる。 -/
theorem deltaRootPerfectoidCandidateCoefficientMap_d (hd : D.IsDistinguished d) :
    letI := deltaRootPrismCommRing D d b
    deltaRootPerfectoidCandidateCoefficientMap D d b hd d = 0 := by
  let := deltaRootPrismCommRing D d b
  change Ideal.Quotient.mk (deltaRootPrism D d b hd).ideal
    (deltaRootPrism D d b hd).generator = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- 元の通常商A/(d)からperfectoid候補への具体的な基底射。 -/
def deltaRootPerfectoidCandidateBaseMap (hd : D.IsDistinguished d) :
    letI := deltaRootPrismCommRing D d b
    A ⧸ Ideal.span {d} →+* DeltaRootPerfectoidCandidate D d b hd := by
  let := deltaRootPrismCommRing D d b
  have hker : Ideal.span {d} ≤
      RingHom.ker (deltaRootPerfectoidCandidateCoefficientMap D d b hd) :=
    Ideal.span_le.mpr (by
      intro x hx
      have hxd : x = d := Set.mem_singleton_iff.mp hx
      subst x
      exact deltaRootPerfectoidCandidateCoefficientMap_d D d b hd)
  exact Ideal.Quotient.lift _ (deltaRootPerfectoidCandidateCoefficientMap D d b hd)
    (fun x hx ↦ hker hx)

/-- 基底射は各商代表の標準係数像と一致する。 -/
theorem deltaRootPerfectoidCandidateBaseMap_mk (hd : D.IsDistinguished d) (x : A) :
    letI := deltaRootPrismCommRing D d b
    deltaRootPerfectoidCandidateBaseMap D d b hd (Ideal.Quotient.mk _ x) =
      deltaRootPerfectoidCandidateCoefficientMap D d b hd x := by
  let := deltaRootPrismCommRing D d b
  simp only [deltaRootPerfectoidCandidateBaseMap, Ideal.Quotient.lift_mk]

/-- perfectoid候補での具体的互換根族。 -/
def deltaRootPerfectoidCandidateRoots (hd : D.IsDistinguished d) :
    letI := deltaRootPrismCommRing D d b
    σ → ℕ → DeltaRootPerfectoidCandidate D d b hd := by
  let := deltaRootPrismCommRing D d b
  exact deltaRootAdjoinCompatibleRoots D d b (deltaRootPrism D d b hd).deltaStructure
    (deltaRootPrism_isPerfect D d b hd) (deltaRootPrismRawMap D d b)
    (Ideal.Quotient.mk (deltaRootPrism D d b hd).ideal)

/-- 互換根族の零段は元の通常商からの基底射による指定元の像。 -/
theorem deltaRootPerfectoidCandidateRoots_zero (hd : D.IsDistinguished d) (s : σ) :
    letI := deltaRootPrismCommRing D d b
    deltaRootPerfectoidCandidateRoots D d b hd s 0 =
      deltaRootPerfectoidCandidateBaseMap D d b hd (Ideal.Quotient.mk _ (b s)) := by
  let := deltaRootPrismCommRing D d b
  rw [deltaRootPerfectoidCandidateBaseMap_mk]
  rfl

/-- 候補内の根族はすべての段で互換p冪根条件を満たす。 -/
theorem deltaRootPerfectoidCandidateRoots_pow (hd : D.IsDistinguished d) (s : σ) (n : ℕ) :
    letI := deltaRootPrismCommRing D d b
    deltaRootPerfectoidCandidateRoots D d b hd s (n + 1) ^ p =
      deltaRootPerfectoidCandidateRoots D d b hd s n := by
  let := deltaRootPrismCommRing D d b
  apply deltaRootAdjoinCompatibleRoots_pow
    D d b _ _ _ _ (deltaRootPrismRawMap_isDeltaHom D d b hd)
  change Ideal.Quotient.mk (deltaRootPrism D d b hd).ideal
    (deltaRootPrism D d b hd).generator = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

end SerrePositivity.BhattScholze
