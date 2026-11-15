module

public import SerrePositivity.AlgebraicGeometry.OpenAtlasStageProperties
public import SerrePositivity.AlgebraicGeometry.CartesianModelEquation

/-!
概要：実際の段の三重交叉上の二つの gluing の式を、同時一致判定の具体的な入力にする。
方針：源・標的・Cartesian 比較と極限での等式を全て既存の検証済みの法則から供給する。
規約：式の存在を追加仮定にせず、段の実際の三重交叉を保持する。
使われ方：G2 の六種の式の同じ段への移送の最後の二つ。
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
/-- 三重交叉の第一の gluing の式を具体的な同時一致判定の入力にする。 -/
def tripleFstEquation (i a c : I) : CartesianModelEquation b where
  sourceModel := pullback (baseChangedOverlapMap γ (m.map i) (m.overlap i a).ι)
    (baseChangedOverlapMap γ (m.map i) (m.overlap i c).ι)
  source := pullback (pullback.fst (j i) (j a)) (pullback.fst (j i) (j c))
  targetModel := pullback γ (m.map a)
  sourceMap := pullback.fst (baseChangedOverlapMap γ (m.map i) (m.overlap i a).ι)
    (baseChangedOverlapMap γ (m.map i) (m.overlap i c).ι) ≫
    baseChangedOverlapMap γ (m.map i) (m.overlap i a).ι ≫ pullback.fst γ (m.map i)
  targetMap := pullback.fst γ (m.map a)
  comparison := m.tripleComparisonAt b γ h i a c
  base := pullback.fst (pullback.fst (j i) (j a)) (pullback.fst (j i) (j c)) ≫
    pullback.fst (j i) (j a) ≫ j i ≫ f
  cartesian := m.isPullback_tripleComparisonAt b γ h i a c
  left := m.stageTriple γ l i a c ≫ baseChangedOverlapMap γ (m.map a) (m.overlap a c).ι
  right := pullback.fst (baseChangedOverlapMap γ (m.map i) (m.overlap i a).ι)
    (baseChangedOverlapMap γ (m.map i) (m.overlap i c).ι) ≫
    m.stageReverse γ l i a ≫ baseChangedOverlapMap γ (m.map a) (m.overlap a i).ι
  leftOver := by rw [Category.assoc, baseChangedOverlapMap_fst, m.stageTriple_toBase γ l hl i a c]
  rightOver := by
    simp only [Category.assoc, baseChangedOverlapMap_fst, m.stageReverse_toBase γ l hl i a]
  atLimit := by simpa only [Category.assoc] using
    m.stageTriple_fst_after_comparison b γ h l hl hn i a c
  sourceQC := (m.finitePresentation_stageTriple γ i a c).2.1
  sourceQS := (m.finitePresentation_stageTriple γ i a c).2.2
  targetFP := (m.finitePresentation_stageChart γ a).1

/-- 三重交叉の第二の gluing の式を具体的な同時一致判定の入力にする。 -/
def tripleSndEquation (i a c : I) : CartesianModelEquation b where
  sourceModel := pullback (baseChangedOverlapMap γ (m.map i) (m.overlap i a).ι)
    (baseChangedOverlapMap γ (m.map i) (m.overlap i c).ι)
  source := pullback (pullback.fst (j i) (j a)) (pullback.fst (j i) (j c))
  targetModel := pullback γ (m.map c)
  sourceMap := pullback.fst (baseChangedOverlapMap γ (m.map i) (m.overlap i a).ι)
    (baseChangedOverlapMap γ (m.map i) (m.overlap i c).ι) ≫
    baseChangedOverlapMap γ (m.map i) (m.overlap i a).ι ≫ pullback.fst γ (m.map i)
  targetMap := pullback.fst γ (m.map c)
  comparison := m.tripleComparisonAt b γ h i a c
  base := pullback.fst (pullback.fst (j i) (j a)) (pullback.fst (j i) (j c)) ≫
    pullback.fst (j i) (j a) ≫ j i ≫ f
  cartesian := m.isPullback_tripleComparisonAt b γ h i a c
  left := m.stageTriple γ l i a c ≫ m.stageReverse γ l a c ≫
    baseChangedOverlapMap γ (m.map c) (m.overlap c a).ι
  right := pullback.snd (baseChangedOverlapMap γ (m.map i) (m.overlap i a).ι)
    (baseChangedOverlapMap γ (m.map i) (m.overlap i c).ι) ≫
    m.stageReverse γ l i c ≫ baseChangedOverlapMap γ (m.map c) (m.overlap c i).ι
  leftOver := by
    simp only [Category.assoc, baseChangedOverlapMap_fst, m.stageReverse_toBase γ l hl a c,
      m.stageTriple_toBase γ l hl i a c]
  rightOver := by
    simp only [Category.assoc, baseChangedOverlapMap_fst, m.stageReverse_toBase γ l hl i c]
    have hc := congrArg (fun z ↦ z ≫ pullback.fst γ (m.map i))
      (pullback.condition
        (f := baseChangedOverlapMap γ (m.map i) (m.overlap i a).ι)
        (g := baseChangedOverlapMap γ (m.map i) (m.overlap i c).ι))
    simpa only [Category.assoc, baseChangedOverlapMap_fst] using hc.symm
  atLimit := by simpa only [Category.assoc] using
    m.stageTriple_snd_after_comparison b γ h l hl hn i a c
  sourceQC := (m.finitePresentation_stageTriple γ i a c).2.1
  sourceQS := (m.finitePresentation_stageTriple γ i a c).2.2
  targetFP := (m.finitePresentation_stageChart γ c).1

end SerrePositivity.AlgebraicGeometry.OpenAtlasModelData
