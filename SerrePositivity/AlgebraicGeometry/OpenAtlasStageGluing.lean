module

public import SerrePositivity.AlgebraicGeometry.OpenAtlasEquationStage
public import SerrePositivity.AlgebraicGeometry.BaseChangedTransitionEquations

/-!
概要：アトラスの六種の具体的な式から、後段の実際の Scheme.GlueData を供給する。
方針：具体的な局所射を組み立て、有限族の各成分を二射影の式へ戻して移送する。
規約：係数射の単射性・忠実平坦性や元の係数環の Noether 性を仮定しない。
使われ方：G2 の一般の有限表示対象の実際の模型の貼り合わせ。
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
/-- 段の実際のチャート・重なり・三種の射を、gluing の係数移送の入力へ入れる。 -/
def transitionCandidate : OpenTransitionCandidate B where
  J := I
  U := fun i ↦ pullback γ (m.map i)
  V := fun ij ↦ pullback γ ((m.overlap ij.1 ij.2).ι ≫ m.map ij.1)
  p := fun i ↦ pullback.fst γ (m.map i)
  q := fun i a ↦ pullback.fst γ ((m.overlap i a).ι ≫ m.map i)
  f := fun i a ↦ baseChangedOverlapMap γ (m.map i) (m.overlap i a).ι
  fOpen := fun i a ↦ isOpenImmersion_baseChangedOverlapMap γ (m.map i) (m.overlap i a).ι
  fOver := fun i a ↦ baseChangedOverlapMap_fst γ (m.map i) (m.overlap i a).ι
  d := m.stageDiagonal γ l
  dOver := m.stageDiagonal_toBase γ l hl
  t := m.stageReverse γ l
  tOver := m.stageReverse_toBase γ l hl
  L := m.stageTriple γ l
  LOver := m.stageTriple_toBase γ l hl

/-- 六種の有限族の底変換射の式を、固定模型への射影の後での式へ戻す。 -/
theorem projectedModelEquations_of_stageEquationsHold {B' : Scheme.{u}} (δ : B' ⟶ B)
    (he : m.stageEquationsHold b γ h l hl hn δ) :
    (m.transitionCandidate γ l hl).ProjectedModelEquations δ := by
  have hex (e : (Fin 3 × I) ⊕ ((I × I) ⊕ (Fin 2 × I × I × I))) :=
    (baseChangedModelArrow_eq_iff δ
      (m.atlasEquationFamily b γ h l hl hn e).sourceMap
      (m.atlasEquationFamily b γ h l hl hn e).targetMap
      (m.atlasEquationFamily b γ h l hl hn e).left
      (m.atlasEquationFamily b γ h l hl hn e).right
      (m.atlasEquationFamily b γ h l hl hn e).leftOver
      (m.atlasEquationFamily b γ h l hl hn e).rightOver).mp (he e)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [Fin.cases_zero, Fin.cases_succ, transitionCandidate, atlasEquationFamily, diagonalRightEquation,
      Category.assoc, Category.comp_id] using hex (.inl (0, i))
  · intro i
    simpa only [Fin.cases_zero, Fin.cases_succ, transitionCandidate, atlasEquationFamily, diagonalLeftEquation,
      Category.assoc, Category.comp_id] using hex (.inl ((0 : Fin 2).succ, i))
  · intro i
    simpa only [Fin.cases_zero, Fin.cases_succ, transitionCandidate, atlasEquationFamily, reverseDiagonalEquation,
      Category.assoc, Category.comp_id] using hex (.inl (((0 : Fin 1).succ).succ, i))
  · intro i a
    simpa only [Fin.cases_zero, Fin.cases_succ, transitionCandidate, atlasEquationFamily, reverseInverseEquation,
      Category.assoc, Category.comp_id] using hex (.inr (.inl (i, a)))
  · intro i a c
    simpa only [Fin.cases_zero, Fin.cases_succ, transitionCandidate, atlasEquationFamily, tripleFstEquation,
      Category.assoc] using hex (.inr (.inr (0, i, a, c)))
  · intro i a c
    simpa only [Fin.cases_zero, Fin.cases_succ, transitionCandidate, atlasEquationFamily, tripleSndEquation,
      Category.assoc] using hex (.inr (.inr ((0 : Fin 1).succ, i, a, c)))

/-- 六種の同時の式から、後段の実際の gluing の式を供給する。 -/
theorem baseChangedEquations_of_stageEquationsHold {B' : Scheme.{u}} (δ : B' ⟶ B)
    (he : m.stageEquationsHold b γ h l hl hn δ) :
    (m.transitionCandidate γ l hl).BaseChangedEquations δ :=
  (m.transitionCandidate γ l hl).baseChangedEquations_of_projected δ
    (m.projectedModelEquations_of_stageEquationsHold b γ h l hl hn δ he)

/-- 六種の同時の式から、実際の後段の Scheme.GlueData を構成する。 -/
def glueDataOfStageEquations {B' : Scheme.{u}} (δ : B' ⟶ B)
    (he : m.stageEquationsHold b γ h l hl hn δ) : Scheme.GlueData.{u} :=
  (m.transitionCandidate γ l hl).baseChangedOpenTransitionGlueData δ
    (m.baseChangedEquations_of_stageEquationsHold b γ h l hl hn δ he)

end SerrePositivity.AlgebraicGeometry.OpenAtlasModelData
