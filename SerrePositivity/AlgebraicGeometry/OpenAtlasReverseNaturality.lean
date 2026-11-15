module

public import SerrePositivity.AlgebraicGeometry.OpenAtlasStageArrows
public import SerrePositivity.AlgebraicGeometry.ModelArrowStageNaturality

/-!
概要：段の反転の自然性から、元の極限上で逆・対角の式が成立することを供給する。
方針：元の二重交叉の比較と段の射の二射影を照合する。
規約：段の係数射の単射性・忠実平坦性は要求しない。
使われ方：G2 の有限個の式を共通する後の段へ降ろす極限側の入力。
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

/-- 元の二重交叉から段の重なりへの実際の比較。 -/
def pairComparisonAt (i a : I) :
    pullback (j i) (j a) ⟶ pullback γ ((m.overlap i a).ι ≫ m.map i) :=
  (m.atlasArrowFamily (.inr (.inl (i, a)))).comparisonAt b γ h

/-- 元の二重交叉の比較と段の開包含の可換式。 -/
theorem pairComparisonAt_toChart (i a : I) :
    m.pairComparisonAt b γ h i a ≫ baseChangedOverlapMap γ (m.map i) (m.overlap i a).ι =
      pullback.fst (j i) (j a) ≫ (m.atlasArrowFamily (.inl i)).comparisonAt b γ h := by
  apply pullback.hom_ext
  · simp [pairComparisonAt, CartesianModelArrow.comparisonAt, atlasArrowFamily, Category.assoc]
  · simp only [Category.assoc, baseChangedOverlapMap_snd]
    simpa only [pairComparisonAt, CartesianModelArrow.comparisonAt, atlasArrowFamily,
      pullback.lift_snd_assoc, pullback.lift_snd] using (m.isPullback_overlapComparison i a).w

variable (l : ∀ e, pullback γ (m.atlasArrowFamily e).sourceMap ⟶
    pullback γ (m.atlasArrowFamily e).targetMap)
  (hl : ∀ e, l e ≫ pullback.fst γ (m.atlasArrowFamily e).targetMap =
    pullback.fst γ (m.atlasArrowFamily e).sourceMap)
  (hn : ∀ e, (m.atlasArrowFamily e).comparisonAt b γ h ≫ l e ≫
    pullback.snd γ (m.atlasArrowFamily e).targetMap = (m.atlasArrowFamily e).arrow)
include hl hn

/-- 元の反転と段の反転は実際の段の標的への射として可換。 -/
theorem stageReverse_naturality (i a : I) :
    m.pairComparisonAt b γ h i a ≫ m.stageReverse γ l i a =
      (pullbackSymmetry (j i) (j a)).hom ≫ m.pairComparisonAt b γ h a i := by
  apply pullback.hom_ext
  · rw [Category.assoc, m.stageReverse_toBase γ l hl i a]
    simp only [pairComparisonAt, CartesianModelArrow.comparisonAt, atlasArrowFamily,
      Category.assoc, pullback.lift_fst, pullbackSymmetry_hom_comp_fst_assoc]
    rw [pullback.condition_assoc]
  · simpa only [pairComparisonAt, stageReverse, atlasArrowFamily, CartesianModelArrow.comparisonAt,
      reverseArrow, Category.assoc, pullback.lift_snd] using hn (.inr (.inl (i, a)))

/-- 段の反転の逆の式は元の二重交叉の比較の後で成立。 -/
theorem stageReverse_inverse_after_comparison (i a : I) :
    m.pairComparisonAt b γ h i a ≫ m.stageReverse γ l i a ≫ m.stageReverse γ l a i =
      m.pairComparisonAt b γ h i a := by
  rw [← Category.assoc, m.stageReverse_naturality b γ h l hl hn i a, Category.assoc,
    m.stageReverse_naturality b γ h l hl hn a i]
  have hs : (pullbackSymmetry (j i) (j a)).hom ≫
      (pullbackSymmetry (j a) (j i)).hom = 𝟙 _ := by
    apply pullback.hom_ext <;> simp
  simp only [← Category.assoc, hs, Category.id_comp]

/-- 対角の反転は元の二重交叉の比較の後で恒等射。 -/
theorem stageReverse_diagonal_after_comparison (i : I) :
    m.pairComparisonAt b γ h i i ≫ m.stageReverse γ l i i = m.pairComparisonAt b γ h i i := by
  rw [m.stageReverse_naturality b γ h l hl hn i i]
  simp

end SerrePositivity.AlgebraicGeometry.OpenAtlasModelData
