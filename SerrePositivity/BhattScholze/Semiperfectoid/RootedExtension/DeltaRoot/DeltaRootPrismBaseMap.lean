module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaRoot.DeltaRootPerfectoidCandidate
public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrismHom

/-! # 根添加prism候補への基底射と標準商射

既存候補への具体的係数射をprism射に束ねる。平坦性は別工程である。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (b : σ → A)

/-- 基底から既存の根添加prism候補の台環への具体的係数射。 -/
def deltaRootPrismCoefficientMap :
    letI := deltaRootPrismCommRing D d b
    A →+* DeltaRootPrismCarrier D d b := by
  letI := deltaRootPrismCommRing D d b
  exact (deltaRootPrismRawMap D d b).comp
    ((deltaAdjoinDivisionMap (polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
      (deltaRootRelationFamily (p := p) b)).comp MvPolynomial.C)

/-- 候補への係数射は、既存の標準δ射を合成したδ射である。 -/
theorem deltaRootPrismCoefficientMap_isDeltaHom (hd : D.IsDistinguished d) :
    let := deltaRootPrismCommRing D d b
    D.IsDeltaHom (deltaRootPrism D d b hd).deltaStructure
      (deltaRootPrismCoefficientMap D d b) := by
  let := deltaRootPrismCommRing D d b
  exact (deltaRootPrismRawMap_isDeltaHom D d b hd).comp
    ((deltaAdjoinDivisionMap_isDeltaHom _ _ _).comp
      (polynomialRankOneDeltaStructure_C_isDeltaHom σ D))

/-- 係数射は基底のdを候補prismの選択生成元そのものへ送る。 -/
theorem deltaRootPrismCoefficientMap_generator (hd : D.IsDistinguished d) :
    letI := deltaRootPrismCommRing D d b
    deltaRootPrismCoefficientMap D d b d = (deltaRootPrism D d b hd).generator := rfl

/-- 基底の主イデアルの像は、候補prismのイデアル全体に一致する。 -/
theorem deltaRootPrismCoefficientMap_ideal (hd : D.IsDistinguished d) :
    let := deltaRootPrismCommRing D d b
    (Ideal.span {d}).map (deltaRootPrismCoefficientMap D d b) =
      (deltaRootPrism D d b hd).ideal := by
  let := deltaRootPrismCommRing D d b
  change (Ideal.span {d}).map (deltaRootPrismCoefficientMap D d b) =
    (deltaRootPrism D d b hd).ideal
  rw [Ideal.map_span, Set.image_singleton, deltaRootPrismCoefficientMap_generator D d b hd]
  rfl

/-- distinguished生成元を持つ元のprismから、既存の根添加prism候補への標準射。 -/
def deltaRootPrismBaseHom (P : OrientedPrism p A)
    (hd : P.deltaStructure.IsDistinguished P.generator) (b : σ → A) :
    letI := deltaRootPrismCommRing P.deltaStructure P.generator b
    OrientedPrism.Hom P (deltaRootPrism P.deltaStructure P.generator b hd) := by
  letI := deltaRootPrismCommRing P.deltaStructure P.generator b
  refine ⟨deltaRootPrismCoefficientMap P.deltaStructure P.generator b,
    deltaRootPrismCoefficientMap_isDeltaHom P.deltaStructure P.generator b hd, ?_⟩
  apply Ideal.map_le_iff_le_comap.mp
  change (Ideal.span {P.generator}).map _ ≤ _
  exact (deltaRootPrismCoefficientMap_ideal P.deltaStructure P.generator b hd).le

/-- 標準prism射の誘導商射は、既存perfectoid候補への基底射に一致する。 -/
theorem deltaRootPrismBaseHom_quotientMap (P : OrientedPrism p A)
    (hd : P.deltaStructure.IsDistinguished P.generator) (b : σ → A) :
    let := deltaRootPrismCommRing P.deltaStructure P.generator b
    (deltaRootPrismBaseHom P hd b).quotientMap =
      deltaRootPerfectoidCandidateBaseMap P.deltaStructure P.generator b hd := by
  let := deltaRootPrismCommRing P.deltaStructure P.generator b
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

end SerrePositivity.BhattScholze
