module

public import SerrePositivity.AlgebraicGeometry.OpenAtlasStageGluing
public import SerrePositivity.AlgebraicGeometry.OpenTransitionAtlasComparison

/-!
概要：具体的なアトラスと後段の六種の式から、実際の有限表示模型と元の対象との比較を供給する。
方針：元の被覆・比較を gluing の比較へ入れ、後段の Noether 性で有限表示性を得る。
規約：元の環の Noether 性は仮定しない。後段の存在は既存の同時一致判定が供給する。
使われ方：G2 の一般の有限表示対象の模型の組立て。
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
/-- 元の被覆・チャート・重なりの比較を、模型全体の比較の入力へ入れる。 -/
def atlasComparison (hcover : ∀ x : X, ∃ i z, j i z = x) :
    OpenTransitionAtlasComparison (m.transitionCandidate γ l hl) b where
  X := X
  f := f
  U := U
  j := j
  jOpen := fun i ↦ inferInstance
  cover := hcover
  chart := fun i ↦ (m.atlasArrowFamily (.inl i)).comparisonAt b γ h
  chartCart := fun i ↦ (m.atlasArrowFamily (.inl i)).isPullback_comparisonAt b γ h
  pair := m.pairComparisonAt b γ h
  pairCart := m.isPullback_pairComparisonAt b γ h
  pairToChart := m.pairComparisonAt_toChart b γ h
  pairReverse := m.stageReverse_toChart_after_comparison b γ h l hl hn

/-- 六種の式を満たす実際の後段で、qcqs な局所有限表示模型と全体の Cartesian 比較を供給する。 -/
theorem exists_glued_model [Finite I]
    (hcover : ∀ x : X, ∃ i z, j i z = x)
    {B' : Scheme.{u}} [IsAffine B'] [IsLocallyNoetherian B']
    (e : Spec (CommRingCat.of R) ⟶ B') (δ : B' ⟶ B) (he : e ≫ δ = b)
    (hEq : m.stageEquationsHold b γ h l hl hn δ) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ B'),
      LocallyOfFinitePresentation p ∧ QuasiCompact p ∧ QuasiSeparated p ∧
        ∃ a : X ⟶ Y, IsPullback a f p e := by
  let C := m.transitionCandidate γ l hl
  let hc := m.baseChangedEquations_of_stageEquationsHold b γ h l hl hn δ hEq
  let A := m.atlasComparison b γ h l hl hn hcover
  letI : Finite C.J := inferInstanceAs (Finite I)
  haveI (i : C.J) : IsAffine (pullback δ (C.p i)) := by
    change IsAffine (pullback δ (pullback.fst γ (m.map i)))
    letI : IsAffine (m.obj i) := m.affine i
    letI : IsAffineHom (m.map i) := inferInstance
    letI : IsAffineHom (pullback.fst γ (m.map i)) :=
      MorphismProperty.pullback_fst (P := @IsAffineHom) γ (m.map i) inferInstance
    letI : IsAffineHom (pullback.fst δ (pullback.fst γ (m.map i))) :=
      MorphismProperty.pullback_fst (P := @IsAffineHom) δ (pullback.fst γ (m.map i)) inferInstance
    exact isAffine_of_isAffineHom (pullback.fst δ (pullback.fst γ (m.map i)))
  have hp (i : C.J) : LocallyOfFinitePresentation (C.p i) :=
    (m.finitePresentation_stageChart γ i).1
  obtain ⟨hfp, hq, hs⟩ := C.finitePresentation_baseChangedToBase δ hc hp
  refine ⟨(C.baseChangedOpenTransitionGlueData δ hc).glued, C.baseChangedToBase δ hc,
    hfp, hq, hs, A.gluedComparison e δ he hc, ?_⟩
  exact A.isPullback_gluedComparison e δ he hc

end SerrePositivity.AlgebraicGeometry.OpenAtlasModelData
