module

public import SerrePositivity.AlgebraicGeometry.OpenAtlasDiagonalNaturality
public import SerrePositivity.AlgebraicGeometry.OpenAtlasStageProperties
public import SerrePositivity.AlgebraicGeometry.CartesianModelEquation

/-!
概要：段の対角・反転の四種の式を具体的な有限族の一致判定の入力へ入れる。
方針：実際の比較・Cartesian 性・有限表示性・極限での式を構造体へ組み立てる。
規約：元の式の存在を新たな仮定にせず、検証済みの法則から供給する。
使われ方：G2 の六種の式の同じ段への移送。
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
/-- 対角の右逆の式を具体的な有限段への一致判定の入力にする。 -/
def diagonalRightEquation (i : I) : CartesianModelEquation b where
  sourceModel := pullback γ (m.map i)
  source := U i
  targetModel := pullback γ (m.map i)
  sourceMap := pullback.fst γ (m.map i)
  targetMap := pullback.fst γ (m.map i)
  comparison := (m.atlasArrowFamily (.inl i)).comparisonAt b γ h
  base := j i ≫ f
  cartesian := (m.atlasArrowFamily (.inl i)).isPullback_comparisonAt b γ h
  left := m.stageDiagonal γ l i ≫ baseChangedOverlapMap γ (m.map i) (m.overlap i i).ι
  right := 𝟙 _
  leftOver := by
    rw [Category.assoc, baseChangedOverlapMap_fst, m.stageDiagonal_toBase γ l hl i]
  rightOver := by simp
  atLimit := by simpa only [Category.comp_id, Category.assoc] using
    m.stageDiagonal_right_inverse_after_comparison b γ h l hl hn i
  sourceQC := (m.finitePresentation_stageChart γ i).2.1
  sourceQS := (m.finitePresentation_stageChart γ i).2.2
  targetFP := (m.finitePresentation_stageChart γ i).1

/-- 対角の左逆の式を具体的な有限段への一致判定の入力にする。 -/
def diagonalLeftEquation (i : I) : CartesianModelEquation b where
  sourceModel := pullback γ ((m.overlap i i).ι ≫ m.map i)
  source := pullback (j i) (j i)
  targetModel := pullback γ ((m.overlap i i).ι ≫ m.map i)
  sourceMap := pullback.fst γ ((m.overlap i i).ι ≫ m.map i)
  targetMap := pullback.fst γ ((m.overlap i i).ι ≫ m.map i)
  comparison := m.pairComparisonAt b γ h i i
  base := pullback.fst (j i) (j i) ≫ j i ≫ f
  cartesian := m.isPullback_pairComparisonAt b γ h i i
  left := baseChangedOverlapMap γ (m.map i) (m.overlap i i).ι ≫ m.stageDiagonal γ l i
  right := 𝟙 _
  leftOver := by rw [Category.assoc, m.stageDiagonal_toBase γ l hl i, baseChangedOverlapMap_fst]
  rightOver := by simp
  atLimit := by simpa only [Category.comp_id, Category.assoc] using
    m.stageDiagonal_left_inverse_after_comparison b γ h l hl hn i
  sourceQC := (m.finitePresentation_stagePair γ i i).2.1
  sourceQS := (m.finitePresentation_stagePair γ i i).2.2
  targetFP := (m.finitePresentation_stagePair γ i i).1

/-- 対角の反転の式を具体的な有限段への一致判定の入力にする。 -/
def reverseDiagonalEquation (i : I) : CartesianModelEquation b where
  sourceModel := pullback γ ((m.overlap i i).ι ≫ m.map i)
  source := pullback (j i) (j i)
  targetModel := pullback γ ((m.overlap i i).ι ≫ m.map i)
  sourceMap := pullback.fst γ ((m.overlap i i).ι ≫ m.map i)
  targetMap := pullback.fst γ ((m.overlap i i).ι ≫ m.map i)
  comparison := m.pairComparisonAt b γ h i i
  base := pullback.fst (j i) (j i) ≫ j i ≫ f
  cartesian := m.isPullback_pairComparisonAt b γ h i i
  left := m.stageReverse γ l i i
  right := 𝟙 _
  leftOver := m.stageReverse_toBase γ l hl i i
  rightOver := by simp
  atLimit := by simpa only [Category.comp_id] using
    m.stageReverse_diagonal_after_comparison b γ h l hl hn i
  sourceQC := (m.finitePresentation_stagePair γ i i).2.1
  sourceQS := (m.finitePresentation_stagePair γ i i).2.2
  targetFP := (m.finitePresentation_stagePair γ i i).1

/-- 反転の逆の式を具体的な有限段への一致判定の入力にする。 -/
def reverseInverseEquation (i a : I) : CartesianModelEquation b where
  sourceModel := pullback γ ((m.overlap i a).ι ≫ m.map i)
  source := pullback (j i) (j a)
  targetModel := pullback γ ((m.overlap i a).ι ≫ m.map i)
  sourceMap := pullback.fst γ ((m.overlap i a).ι ≫ m.map i)
  targetMap := pullback.fst γ ((m.overlap i a).ι ≫ m.map i)
  comparison := m.pairComparisonAt b γ h i a
  base := pullback.fst (j i) (j a) ≫ j i ≫ f
  cartesian := m.isPullback_pairComparisonAt b γ h i a
  left := m.stageReverse γ l i a ≫ m.stageReverse γ l a i
  right := 𝟙 _
  leftOver := by rw [Category.assoc, m.stageReverse_toBase γ l hl a i,
    m.stageReverse_toBase γ l hl i a]
  rightOver := by simp
  atLimit := by simpa only [Category.comp_id, Category.assoc] using
    m.stageReverse_inverse_after_comparison b γ h l hl hn i a
  sourceQC := (m.finitePresentation_stagePair γ i a).2.1
  sourceQS := (m.finitePresentation_stagePair γ i a).2.2
  targetFP := (m.finitePresentation_stagePair γ i a).1

end SerrePositivity.AlgebraicGeometry.OpenAtlasModelData
