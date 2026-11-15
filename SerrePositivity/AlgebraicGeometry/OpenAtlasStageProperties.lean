module

public import SerrePositivity.AlgebraicGeometry.OpenAtlasTripleNaturality

/-!
概要：段の実際のチャート・重なり・三重交叉の有限表示性と元の対象との Cartesian 比較。
方針：既存の模型の底変換と、三重交叉の具体的な同型で性質を移送する。
規約：基底 B は任意で元の環の Noether 性を要求しない。
使われ方：G2 の六種の式の共通段への一致判定の実際の源と標的。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry.OpenAtlasModelData
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u v
variable {k : Type v} [CommRing k] [IsNoetherianRing k]
  {R : Type u} [CommRing R] [Algebra k R]
  {I : Type u} {X : Scheme.{u}} {U : I → Scheme.{u}} {j : ∀ i, U i ⟶ X}
  [∀ i, IsOpenImmersion (j i)] {f : X ⟶ Spec (CommRingCat.of R)}
  (m : OpenAtlasModelData k U j f)
  {B : Scheme.{u}} (b : Spec (CommRingCat.of R) ⟶ B)
  (γ : B ⟶ Spec (CommRingCat.of m.A))
  (h : b ≫ γ = Spec.map (CommRingCat.ofHom (algebraMap m.A R)))

/-- 元の二重交叉と段の重なりの比較は Cartesian。 -/
theorem isPullback_pairComparisonAt (i a : I) :
    IsPullback (m.pairComparisonAt b γ h i a) (pullback.fst (j i) (j a) ≫ j i ≫ f)
      (pullback.fst γ ((m.overlap i a).ι ≫ m.map i)) b :=
  (m.atlasArrowFamily (.inr (.inl (i, a)))).isPullback_comparisonAt b γ h

/-- 元の三重交叉と段の実際の三重交叉の比較は Cartesian。 -/
theorem isPullback_tripleComparisonAt (i a c : I) :
    IsPullback (m.tripleComparisonAt b γ h i a c)
      (pullback.fst (pullback.fst (j i) (j a)) (pullback.fst (j i) (j c)) ≫
        pullback.fst (j i) (j a) ≫ j i ≫ f)
      (pullback.fst (baseChangedOverlapMap γ (m.map i) (m.overlap i a).ι)
        (baseChangedOverlapMap γ (m.map i) (m.overlap i c).ι) ≫
        baseChangedOverlapMap γ (m.map i) (m.overlap i a).ι ≫ pullback.fst γ (m.map i)) b := by
  let e := baseChangedOverlapTripleIso γ (m.map i) (m.overlap i a).ι (m.overlap i c).ι
  have hb : (m.atlasArrowFamily (.inr (.inr (i, a, c)))).comparisonAt b γ h ≫ e.inv =
      m.tripleComparisonAt b γ h i a c := by
    rw [← m.tripleComparisonAt_iso b γ h i a c, Category.assoc]
    simp only [e, Iso.hom_inv_id, Category.comp_id]
  have he : e.inv ≫
      (pullback.fst (baseChangedOverlapMap γ (m.map i) (m.overlap i a).ι)
        (baseChangedOverlapMap γ (m.map i) (m.overlap i c).ι) ≫
        baseChangedOverlapMap γ (m.map i) (m.overlap i a).ι ≫ pullback.fst γ (m.map i)) =
      pullback.fst γ (pullback.fst (m.overlap i a).ι (m.overlap i c).ι ≫
        (m.overlap i a).ι ≫ m.map i) := by
    calc
      _ = e.inv ≫ (e.hom ≫ pullback.fst γ
          (pullback.fst (m.overlap i a).ι (m.overlap i c).ι ≫ (m.overlap i a).ι ≫ m.map i)) :=
        congrArg (fun z ↦ e.inv ≫ z)
          (baseChangedOverlapTripleIso_hom_fst γ (m.map i) (m.overlap i a).ι (m.overlap i c).ι).symm
      _ = _ := e.inv_hom_id_assoc _
  have hold : IsPullback
      ((m.atlasArrowFamily (.inr (.inr (i, a, c)))).comparisonAt b γ h)
      (pullback.fst (pullback.fst (j i) (j a)) (pullback.fst (j i) (j c)) ≫
        pullback.fst (j i) (j a) ≫ j i ≫ f)
      (pullback.fst γ (pullback.fst (m.overlap i a).ι (m.overlap i c).ι ≫
        (m.overlap i a).ι ≫ m.map i)) b := by
    simpa only [atlasArrowFamily] using
      (m.atlasArrowFamily (.inr (.inr (i, a, c)))).isPullback_comparisonAt b γ h
  apply hold.of_iso
    (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
  · simpa only [Iso.refl_hom, Iso.symm_hom, Category.id_comp] using hb
  · simp
  · simpa only [Iso.refl_hom, Iso.symm_hom, Category.comp_id] using he.symm
  · simp

/-- 段のチャートは段の基底上 qcqs・局所有限表示。 -/
theorem finitePresentation_stageChart (i : I) :
    LocallyOfFinitePresentation (pullback.fst γ (m.map i)) ∧
      QuasiCompact (pullback.fst γ (m.map i)) ∧ QuasiSeparated (pullback.fst γ (m.map i)) := by
  letI : LocallyOfFinitePresentation (m.map i) := m.fp i
  letI : QuasiCompact (m.map i) := m.qc i
  letI : QuasiSeparated (m.map i) := m.qs i
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- 段の重なりは段の基底上 qcqs・局所有限表示。 -/
theorem finitePresentation_stagePair (i a : I) :
    LocallyOfFinitePresentation (pullback.fst γ ((m.overlap i a).ι ≫ m.map i)) ∧
      QuasiCompact (pullback.fst γ ((m.overlap i a).ι ≫ m.map i)) ∧
      QuasiSeparated (pullback.fst γ ((m.overlap i a).ι ≫ m.map i)) := by
  obtain ⟨hf, hq, hs⟩ := m.finitePresentation_overlap i a
  letI := hf
  letI := hq
  letI := hs
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- 段の実際の三重交叉も段の基底上 qcqs・局所有限表示。 -/
theorem finitePresentation_stageTriple (i a c : I) :
    LocallyOfFinitePresentation
      (pullback.fst (baseChangedOverlapMap γ (m.map i) (m.overlap i a).ι)
        (baseChangedOverlapMap γ (m.map i) (m.overlap i c).ι) ≫
        baseChangedOverlapMap γ (m.map i) (m.overlap i a).ι ≫ pullback.fst γ (m.map i)) ∧
    QuasiCompact
      (pullback.fst (baseChangedOverlapMap γ (m.map i) (m.overlap i a).ι)
        (baseChangedOverlapMap γ (m.map i) (m.overlap i c).ι) ≫
        baseChangedOverlapMap γ (m.map i) (m.overlap i a).ι ≫ pullback.fst γ (m.map i)) ∧
    QuasiSeparated
      (pullback.fst (baseChangedOverlapMap γ (m.map i) (m.overlap i a).ι)
        (baseChangedOverlapMap γ (m.map i) (m.overlap i c).ι) ≫
        baseChangedOverlapMap γ (m.map i) (m.overlap i a).ι ≫ pullback.fst γ (m.map i)) := by
  obtain ⟨hf, hq, hs⟩ := m.finitePresentation_triple i a c
  letI := hf
  letI := hq
  letI := hs
  rw [← baseChangedOverlapTripleIso_hom_fst]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end SerrePositivity.AlgebraicGeometry.OpenAtlasModelData
