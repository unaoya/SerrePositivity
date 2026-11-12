module

public import SerrePositivity.KST.NonConnective.SequentialSpectrum
public import SerrePositivity.KST.Spectra.RawSpectrumMappingSourceFunctor
public import SerrePositivity.KST.Spectra.RawSpectrumMappingAcyclic
public import SerrePositivity.KST.Spectra.RawSpectrumHomPoints
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanCoefficientFibration

/-!
概要：逐次列から固定 Kan 列への全写像空間の反変図式と BF 置換射影。
方針：元の RawSpectrumMapping の前合成・後合成を全単体で使う。
規約：整合した end を持ち上げる準備であり、点ごとの選択の自然性を仮定しない。
使われ方：K-7 の実 coherent Sp 余錐。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective

/-- 元の逐次 BF 列から固定 Kan 列への反変な全 Hom 図式。 -/
abbrev sequentialRawHomDiagram (D : SpectrumSequence.{u}) (Z : KanSequence.{u}) :
    SequentialIndex.{u}ᵒᵖ ⥤ SSet.{u} :=
  D.op ⋙ RawSpectrumMapping.sourceFunctor Z ⋙ PointedSimplicialSet.forget

/-- Kan 列の後合成を、元の全 Hom 図式の自然変換として保持する。 -/
def sequentialRawHomPost (D : SpectrumSequence.{u}) {Y Z : KanSequence.{u}} (p : Y ⟶ Z) :
    sequentialRawHomDiagram D Y ⟶ sequentialRawHomDiagram D Z where
  app i := RawSpectrumMapping.post (D.obj i.unop) p
  naturality i j f := by
    exact (congrArg Under.Hom.right
      (RawSpectrumMapping.pointedPre_post (D.map f.unop) p)).symm

/-- 段ごとの全単射 RLP は、元の全 Hom 図式の各成分でも全単射 RLP。 -/
lemma sequentialRawHomPost_trivial (D : SpectrumSequence.{u})
    {Y Z : KanSequence.{u}} (p : Y ⟶ Z)
    (hp : ∀ k, (MorphismProperty.monomorphisms SSet.{u}).rlp (p.app k).right)
    (i : SequentialIndex.{u}ᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((sequentialRawHomPost D p).app i) :=
  RawSpectrumMapping.post_trivialKanFibration (D.obj i.unop) p hp

/-- 元の厳密な Kan 列射を、同じ全 Hom の零単体として表示する。 -/
def sequentialRawHomVertex (X : OmegaSpectrum.{u}) (Z : KanSequence.{u})
    (f : KanSequence.Hom X.toKanSequence Z) : (RawSpectrumMapping.space X Z) _⦋0⦌ :=
  PointedSimplicialSet.unitVertexEquiv _ (RawSpectrumMapping.homPoint X Z f)

/-- 上の零単体を一段で評価すると元の点つき段射。 -/
lemma sequentialRawHomVertex_evaluation (X : OmegaSpectrum.{u}) (Z : KanSequence.{u})
    (f : KanSequence.Hom X.toKanSequence Z) (k : ℕ) :
    (RawSpectrumMapping.evaluation X Z k).app _ (sequentialRawHomVertex X Z f) =
      pointedHomVertexEquiv _ _ (f.app k) := by
  change (RawSpectrumMapping.pointedEvaluation X Z k).right.app _
    (PointedSimplicialSet.unitVertexEquiv _ (RawSpectrumMapping.homPoint X Z f)) = _
  rw [← PointedSimplicialSet.unitVertexEquiv_naturality,
    RawSpectrumMapping.homPoint_evaluation]
  rfl

/-- 段ごとの標準注入を点として表した、元の反変 Hom 図式の厳密錐。 -/
def sequentialRawInjectionCone (D : SpectrumSequence.{u}) :
    Cone (sequentialRawHomDiagram D (OmegaSpectrum.filteredKanSequence D)) where
  pt := Δ[0]
  π := {
    app i := SSet.yonedaEquiv.symm (sequentialRawHomVertex (D.obj i.unop)
      (OmegaSpectrum.filteredKanSequence D) (OmegaSpectrum.filteredKanInjection D i.unop))
    naturality i j f := by
      apply RawSpectrumMapping.hom_ext
      intro k
      change (𝟙 _ ≫ _) ≫ _ =
        (_ ≫ RawSpectrumMapping.pre (D.map f.unop) (OmegaSpectrum.filteredKanSequence D)) ≫ _
      dsimp only [Functor.op]
      rw [Category.id_comp, Category.assoc,
        RawSpectrumMapping.pre_evaluation (D.map f.unop) (OmegaSpectrum.filteredKanSequence D) k]
      let vi := sequentialRawHomVertex (D.obj i.unop) (OmegaSpectrum.filteredKanSequence D)
        (OmegaSpectrum.filteredKanInjection D i.unop)
      let vj := sequentialRawHomVertex (D.obj j.unop) (OmegaSpectrum.filteredKanSequence D)
        (OmegaSpectrum.filteredKanInjection D j.unop)
      have ei : (RawSpectrumMapping.evaluation (D.obj i.unop)
          (OmegaSpectrum.filteredKanSequence D) k).app _ vi =
          pointedHomVertexEquiv _ _ (colimit.ι (OmegaSpectrum.levelDiagram D k) i.unop) :=
        sequentialRawHomVertex_evaluation _ _ _ _
      have ej : (RawSpectrumMapping.evaluation (D.obj j.unop)
          (OmegaSpectrum.filteredKanSequence D) k).app _ vj =
          pointedHomVertexEquiv _ _ (colimit.ι (OmegaSpectrum.levelDiagram D k) j.unop) :=
        sequentialRawHomVertex_evaluation _ _ _ _
      have hv : (RawSpectrumMapping.evaluation (D.obj j.unop)
          (OmegaSpectrum.filteredKanSequence D) k).app _ vj =
          (RawSpectrumMapping.evaluation (D.obj i.unop) (OmegaSpectrum.filteredKanSequence D) k ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((D.map f.unop).app k)
              ((OmegaSpectrum.filteredKanSequence D).level k).space).app _ vi := by
        change _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((D.map f.unop).app k) _).app _
          ((RawSpectrumMapping.evaluation (D.obj i.unop)
            (OmegaSpectrum.filteredKanSequence D) k).app _ vi)
        rw [ei, ej]
        exact (congrArg (pointedHomVertexEquiv _ _)
          (colimit.w (OmegaSpectrum.levelDiagram D k) f.unop).symm).trans
            (pointedHomVertexEquiv_pre ((D.map f.unop).app k)
              (colimit.ι (OmegaSpectrum.levelDiagram D k) i.unop)).symm
      exact (SSet.yonedaEquiv_symm_comp vj _).trans
        ((congrArg SSet.yonedaEquiv.symm hv).trans
          (SSet.yonedaEquiv_symm_comp vi _).symm) }

end SerrePositivity.KST.NonConnective
