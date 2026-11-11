module

public import SerrePositivity.KST.Spectra.SpectrumMappingAdjointCoordinates
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomAdjointPreRestriction
public import SerrePositivity.KST.Spectra.KanAdjointNaturality
public import SerrePositivity.KST.Spectra.PostMappingLifts

/-!
概要：Kan 円への随伴構造射の自然性を、元の全 Hom 単体集合上のホモトピーとして構成する。
方針：通常の円への制限で厳密な段条件へ戻し、自明 RLP を全 Hom パラメータに適用する。
規約：個々の BF 射の成分だけに制限しない。使われ方：loop 比較の豊穣な自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 全パラメータの自然性の二つの像を置く、元の二重の点つき Hom。 -/
abbrev kanAdjointParameterTarget (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    PointedSimplicialSet.{u} :=
  PointedObject.basedHom (X.level n).space
    (PointedObject.basedHom CirclePower.space (Y.level (n + 1)).space)

/-- 元の全 Hom の n 段評価を、標的の Kan 随伴へ後合成する。 -/
def kanAdjointParameterLeft (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    pointedSpace X Y.toKanSequence ⟶ kanAdjointParameterTarget X Y n :=
  pointedEvaluation X Y.toKanSequence n ≫
    PointedObject.basedHomMap (X.level n).space (KanSequence.kanAdjoint Y.toKanSequence n)

/-- 元の一段先の全 Hom を、源の Kan 随伴の評価へ前合成して二度 curry する。 -/
def kanAdjointParameterRight (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    pointedSpace X Y.toKanSequence ⟶ kanAdjointParameterTarget X Y n :=
  pointedEvaluation X Y.toKanSequence (n + 1) ≫
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (uncurry (KanSequence.kanAdjoint X.toKanSequence n))
      (Y.level (n + 1)).space ≫
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso CirclePower.space (X.level n).space (Y.level (n + 1)).space).hom

/-- 二つの全パラメータの像を通常の円へ制限する、元の二重 Hom の射。 -/
def kanAdjointParameterRestriction (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    kanAdjointParameterTarget X Y n ⟶
      PointedObject.basedHom (X.level n).space
        (PointedObject.basedHom PointedSimplicialSet.circle (Y.level (n + 1)).space) :=
  PointedObject.basedHomMap (X.level n).space
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} (Y.level (n + 1)).space)

/-- 標的の随伴への後合成は、通常の円への制限で元の随伴への後合成に戻る。 -/
lemma kanAdjointParameterLeft_restriction (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    kanAdjointParameterLeft X Y n ≫ kanAdjointParameterRestriction X Y n =
    pointedEvaluation X Y.toKanSequence n ≫ PointedObject.basedHomMap (X.level n).space
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (Y.level n).space (Y.level (n + 1)).space (Y.sigma n)) := by
  have h := congrArg ((ihom (X.level n).space).map)
    (KanSequence.kanAdjoint_comparison Y.toKanSequence n)
  have h' := congrArg (pointedEvaluation X Y.toKanSequence n ≫ ·) h
  simp only [Functor.map_comp] at h'
  exact h'

/-- 源の Kan 随伴の評価への前合成も、通常の円への制限で同じ元の段条件に戻る。 -/
lemma kanAdjointParameterRight_restriction (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    kanAdjointParameterRight X Y n ≫ kanAdjointParameterRestriction X Y n =
    pointedEvaluation X Y.toKanSequence n ≫ PointedObject.basedHomMap (X.level n).space
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (Y.level n).space (Y.level (n + 1)).space (Y.sigma n)) := by
  have ha : KanSequence.kanAdjoint X.toKanSequence n ≫
      (pre CirclePower.unit.{u}).app (X.level (n + 1)).space = curry (X.sigma n) := by
    rw [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
    exact KanSequence.kanAdjoint_comparison X.toKanSequence n
  have h := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.adjoint_pre_restriction CirclePower.unit
    (KanSequence.kanAdjoint X.toKanSequence n) (X.sigma n) ha (Y.level (n + 1)).space
  unfold kanAdjointParameterRight kanAdjointParameterRestriction
  simp only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, Category.assoc]
  have h' := congrArg (pointedEvaluation X Y.toKanSequence (n + 1) ≫ ·) h
  have hc := pointedEvaluation_adjoint_condition X Y n
  simp only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hc
  exact h'.trans hc

/-- 通常の円への制限は、二重 Hom の全ての単射への RLP を持つ。 -/
lemma kanAdjointParameterRestriction_rlp (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp
      (kanAdjointParameterRestriction X Y n).right :=
  PointedMapping.post_rlp_monomorphisms _ _
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.anodyne_prePointed_rlp CirclePower.unit
      (PointedKanReplacement.unit_anodyne PointedSimplicialSet.circle) _)

/-- 全 Hom の基点を固定し、通常の円への制限も全区間で元の厳密な式に保つ。 -/
lemma kanAdjointParameter_vertical_naturality (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    ∃ H : SSet.Homotopy (kanAdjointParameterLeft X Y n).right
        (kanAdjointParameterRight X Y n).right,
      H.h ≫ (kanAdjointParameterRestriction X Y n).right =
        fst (pointedSpace X Y.toKanSequence).right (Δ[1] : SSet.{u}) ≫
          (kanAdjointParameterLeft X Y n).right ≫ (kanAdjointParameterRestriction X Y n).right ∧
      (pointedSpace X Y.toKanSequence).hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ (kanAdjointParameterTarget X Y n).hom := by
  let M := pointedSpace X Y.toKanSequence
  let f := kanAdjointParameterLeft X Y n
  let g := kanAdjointParameterRight X Y n
  let p := kanAdjointParameterRestriction X Y n
  let baseMono : Mono M.hom := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basepoint_mono M
  have he : f ≫ p = g ≫ p :=
    (kanAdjointParameterLeft_restriction X Y n).trans
      (kanAdjointParameterRight_restriction X Y n).symm
  have hb : M.hom ≫ f.right = M.hom ≫ g.right := by
    rw [Under.w f, Under.w g]
  obtain ⟨H, hH, hB⟩ :=
    MonoRightLiftingRelativeHomotopy.exists_relative_vertical_homotopy
      p.right (kanAdjointParameterRestriction_rlp X Y n) M.hom f.right g.right
      (congrArg Under.Hom.right he) hb
  refine ⟨H, hH, ?_⟩
  rw [hB, Under.w f]
  rfl

/-- 元の全 Hom パラメータで選んだ、基点固定かつ通常の円の上で垂直なホモトピー。 -/
def kanAdjointParameterHomotopy (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    SSet.Homotopy (kanAdjointParameterLeft X Y n).right
      (kanAdjointParameterRight X Y n).right :=
  (kanAdjointParameter_vertical_naturality X Y n).choose

/-- 選んだ全パラメータのホモトピーは、通常の円への制限を全区間で保つ。 -/
lemma kanAdjointParameterHomotopy_restriction (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    (kanAdjointParameterHomotopy X Y n).h ≫ (kanAdjointParameterRestriction X Y n).right =
      fst (pointedSpace X Y.toKanSequence).right (Δ[1] : SSet.{u}) ≫
        (kanAdjointParameterLeft X Y n).right ≫ (kanAdjointParameterRestriction X Y n).right :=
  (kanAdjointParameter_vertical_naturality X Y n).choose_spec.1

/-- 選んだ全パラメータのホモトピーは、元の零 Hom の基点を全区間で固定する。 -/
lemma kanAdjointParameterHomotopy_base (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    (pointedSpace X Y.toKanSequence).hom ▷ (Δ[1] : SSet.{u}) ≫
      (kanAdjointParameterHomotopy X Y n).h =
    toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ (kanAdjointParameterTarget X Y n).hom :=
  (kanAdjointParameter_vertical_naturality X Y n).choose_spec.2

end SerrePositivity.KST.Spectra.RawSpectrumMapping
