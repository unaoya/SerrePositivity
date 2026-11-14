module

public import SerrePositivity.AlgebraicGeometry.OpenAtlasTripleComparisonAt

/-!
概要：元の三重交叉の射の自然性と gluing の二つの式を、実際の段の射で供給する。
方針：具体的な三重交叉の同型を通した自然性を二射影で確認し、元の射影の式を合成する。
規約：式は元の比較の後の式。有限段全体での式は後の一致判定へ渡す。
使われ方：G2 の六種の式の極限側の入力の最後の二つ。
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

variable (l : ∀ e, pullback γ (m.atlasArrowFamily e).sourceMap ⟶
    pullback γ (m.atlasArrowFamily e).targetMap)
  (hl : ∀ e, l e ≫ pullback.fst γ (m.atlasArrowFamily e).targetMap =
    pullback.fst γ (m.atlasArrowFamily e).sourceMap)
  (hn : ∀ e, (m.atlasArrowFamily e).comparisonAt b γ h ≫ l e ≫
    pullback.snd γ (m.atlasArrowFamily e).targetMap = (m.atlasArrowFamily e).arrow)
include hl hn

/-- 元の反転の比較と段の開包含の合成は、元の第二射影とチャート比較に等しい。 -/
@[reassoc] theorem stageReverse_toChart_after_comparison (i a : I) :
    m.pairComparisonAt b γ h i a ≫ m.stageReverse γ l i a ≫
        baseChangedOverlapMap γ (m.map a) (m.overlap a i).ι =
      pullback.snd (j i) (j a) ≫
          ((m.atlasArrowFamily (.inl a)).comparisonAt b γ h : U a ⟶ pullback γ (m.map a)) := by
  rw [← Category.assoc, m.stageReverse_naturality b γ h l hl hn i a,
    Category.assoc, m.pairComparisonAt_toChart b γ h a i]
  simp

/-- 元の三重交叉の射と段の射は実際の段の標的への射として可換。 -/
theorem stageTriple_naturality (i a c : I) :
    m.tripleComparisonAt b γ h i a c ≫ m.stageTriple γ l i a c =
      tripleNextPair (j := j) i a c ≫ m.pairComparisonAt b γ h a c := by
  apply pullback.hom_ext
  · rw [Category.assoc, m.stageTriple_toBase γ l hl i a c]
    simp only [tripleComparisonAt, pairComparisonAt, CartesianModelArrow.comparisonAt,
      atlasArrowFamily, tripleNextPair, Category.assoc, pullback.lift_fst_assoc,
      pullback.lift_fst, baseChangedOverlapMap_fst]
    rw [← pullback.condition_assoc]
  · simp only [stageTriple, ← Category.assoc]
    rw [m.tripleComparisonAt_iso b γ h i a c]
    simpa only [pairComparisonAt, CartesianModelArrow.comparisonAt, atlasArrowFamily,
      tripleArrow, Category.assoc, pullback.lift_snd] using hn (.inr (.inr (i, a, c)))

/-- 三重交叉の第一の gluing の式は、元の三重交叉の比較の後で成立。 -/
theorem stageTriple_fst_after_comparison (i a c : I) :
    m.tripleComparisonAt b γ h i a c ≫ m.stageTriple γ l i a c ≫
        baseChangedOverlapMap γ (m.map a) (m.overlap a c).ι =
      m.tripleComparisonAt b γ h i a c ≫
        pullback.fst (baseChangedOverlapMap γ (m.map i) (m.overlap i a).ι)
          (baseChangedOverlapMap γ (m.map i) (m.overlap i c).ι) ≫
        m.stageReverse γ l i a ≫ baseChangedOverlapMap γ (m.map a) (m.overlap a i).ι := by
  calc
    _ = tripleNextPair (j := j) i a c ≫ m.pairComparisonAt b γ h a c ≫
        baseChangedOverlapMap γ (m.map a) (m.overlap a c).ι := by
      rw [← Category.assoc, m.stageTriple_naturality b γ h l hl hn i a c, Category.assoc]
    _ = pullback.fst (pullback.fst (j i) (j a)) (pullback.fst (j i) (j c)) ≫
        pullback.snd (j i) (j a) ≫
          ((m.atlasArrowFamily (.inl a)).comparisonAt b γ h : U a ⟶ pullback γ (m.map a)) := by
      rw [m.pairComparisonAt_toChart b γ h a c]
      simp [tripleNextPair, Category.assoc]
    _ = pullback.fst (pullback.fst (j i) (j a)) (pullback.fst (j i) (j c)) ≫
        (m.pairComparisonAt b γ h i a ≫ m.stageReverse γ l i a ≫
          baseChangedOverlapMap γ (m.map a) (m.overlap a i).ι) := by
      rw [m.stageReverse_toChart_after_comparison b γ h l hl hn i a]
    _ = _ := by simp only [tripleComparisonAt_fst_assoc, Category.assoc]

/-- 三重交叉の第二の gluing の式は、元の三重交叉の比較の後で成立。 -/
theorem stageTriple_snd_after_comparison (i a c : I) :
    m.tripleComparisonAt b γ h i a c ≫ m.stageTriple γ l i a c ≫ m.stageReverse γ l a c ≫
        baseChangedOverlapMap γ (m.map c) (m.overlap c a).ι =
      m.tripleComparisonAt b γ h i a c ≫
        pullback.snd (baseChangedOverlapMap γ (m.map i) (m.overlap i a).ι)
          (baseChangedOverlapMap γ (m.map i) (m.overlap i c).ι) ≫
        m.stageReverse γ l i c ≫ baseChangedOverlapMap γ (m.map c) (m.overlap c i).ι := by
  calc
    _ = tripleNextPair (j := j) i a c ≫ m.pairComparisonAt b γ h a c ≫
        m.stageReverse γ l a c ≫ baseChangedOverlapMap γ (m.map c) (m.overlap c a).ι := by
      rw [← Category.assoc, ← Category.assoc,
        m.stageTriple_naturality b γ h l hl hn i a c, Category.assoc, Category.assoc]
    _ = pullback.snd (pullback.fst (j i) (j a)) (pullback.fst (j i) (j c)) ≫
        pullback.snd (j i) (j c) ≫
          ((m.atlasArrowFamily (.inl c)).comparisonAt b γ h : U c ⟶ pullback γ (m.map c)) := by
      rw [m.stageReverse_toChart_after_comparison b γ h l hl hn a c]
      simp [tripleNextPair, Category.assoc]
    _ = pullback.snd (pullback.fst (j i) (j a)) (pullback.fst (j i) (j c)) ≫
        (m.pairComparisonAt b γ h i c ≫ m.stageReverse γ l i c ≫
          baseChangedOverlapMap γ (m.map c) (m.overlap c i).ι) := by
      rw [m.stageReverse_toChart_after_comparison b γ h l hl hn i c]
    _ = _ := by simp only [tripleComparisonAt_snd_assoc, Category.assoc]

end SerrePositivity.AlgebraicGeometry.OpenAtlasModelData
