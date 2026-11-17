module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SectionBaseChangeReindex
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.JointRealizationPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeSectionDiagramComparison

/-!
概要：相対切断の底変換と、底上の定義域の制限を同じ全族の同型で交換する。
方針：既存joint比較の合成則と豊穣前合成の実現を端点移送の式でつなぐ。
規約：HTT §3.3.2、Kerodon Corollary 5.6.0.6（Tag 028T）の指定構成の法則。
  個別の値の同型を集めず、元の二つの指定実現同型を保持する。
使われ方：S8のP3-B1、単体圏のunderと係数の底変換の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

private def overPreJoint {B : SSet.{u}} {J : Type u} [Category.{u} J]
    {A T : Jᵒᵖ ⥤ Over B} (η : A ⟶ T) :
    KanEnrichedDiagramComparison (relativeSectionEnrichedDiagram T)
      (relativeSectionEnrichedDiagram A) where
  component j := relativeFunctorOverPreComparison (η.app (Opposite.op j))
  naturality f p := (relativeSectionDiagramComparison η p).naturality f

private lemma overPreJoint_iso {B : SSet.{u}} {J : Type u} [Category.{u} J]
    {A T : Jᵒᵖ ⥤ Over B} (η : A ⟶ T)
    (hη : ∀ j (p : LeftFibrationObject B),
      IsQCatEquivalence (relativeFunctorOverPre p.val.hom (η.app (Opposite.op j)))) :
    relativeSectionRealizationComparisonIso η hη = (overPreJoint η).realizationIso hη := by
  rfl

private lemma overPreJoint_baseChange {B D : SSet.{u}} {J : Type u} [Category.{u} J]
    (k : D ⟶ B) {A T : Jᵒᵖ ⥤ Over D} (η : A ⟶ T) :
    jointComparisonTrans (relativeSectionBaseChangeComparison k T)
        (overPreJoint (Functor.whiskerRight η (Over.map k))) =
      jointComparisonTrans
        (jointComparisonPrecompose (overPreJoint η) (leftFibrationBaseChangeEnriched k))
        (relativeSectionBaseChangeComparison k A) := by
  apply jointComparison_ext
  intro j p
  exact (relativeFunctorBaseChangeForward_overPre p.val.hom k
    (η.app (Opposite.op j))).symm

/-- 指定した底変換同型は、底上の定義域の自然変換による制限と全族で両立する。
HTT §3.3.2・Kerodon Tag 028Tの構成の法則を、この相対切断模型で照合する。 -/
@[cite HTT "3.3.2" (partial := special) "相対切断模型における指定底変換と制限の合成則。"]
lemma relativeSectionBaseChangeRealizationIso_overPre {B D : SSet.{u}} {J : Type u} [Category.{u} J]
    (k : D ⟶ B) {A T : Jᵒᵖ ⥤ Over D} (η : A ⟶ T)
    (hη : ∀ j (p : LeftFibrationObject D),
      IsQCatEquivalence (relativeFunctorOverPre p.val.hom (η.app (Opposite.op j))))
    (hηk : ∀ j (p : LeftFibrationObject B),
      IsQCatEquivalence (relativeFunctorOverPre p.val.hom
        ((Functor.whiskerRight η (Over.map k)).app (Opposite.op j)))) :
    relativeSectionBaseChangeRealizationIso k T ≪≫
      relativeSectionRealizationComparisonIso (Functor.whiskerRight η (Over.map k)) hηk =
    (relativeSectionRealizationComparisonIso η hη).precomp
        (leftFibrationInfinityBaseChange k) ≪≫
      relativeSectionBaseChangeRealizationIso k A := by
  let BCT := relativeSectionBaseChangeComparison k T
  let BCA := relativeSectionBaseChangeComparison k A
  let N := overPreJoint η
  let M := overPreJoint (Functor.whiskerRight η (Over.map k))
  let P := jointComparisonPrecompose N (leftFibrationBaseChangeEnriched k)
  let hT := (relativeSectionEnrichedDiagram T).realization_precompose
    (leftFibrationBaseChangeEnriched k)
  let hA := (relativeSectionEnrichedDiagram A).realization_precompose
    (leftFibrationBaseChangeEnriched k)
  let hBCT := relativeSectionBaseChangeComparison_isQCatEquivalence k T
  let hBCA := relativeSectionBaseChangeComparison_isQCatEquivalence k A
  let hP := jointComparisonPrecompose_isQCatEquivalence N
    (leftFibrationBaseChangeEnriched k) hη
  have hraw : BCT.realizationIso hBCT ≪≫ M.realizationIso hηk =
      P.realizationIso hP ≪≫ BCA.realizationIso hBCA := by
    rw [jointRealizationIso_trans BCT M hBCT hηk
        (jointComparisonTrans_isQCatEquivalence BCT M hBCT hηk),
      jointRealizationIso_trans P BCA hP hBCA
        (jointComparisonTrans_isQCatEquivalence P BCA hP hBCA)]
    exact jointRealizationIso_congr (overPreJoint_baseChange k η) _ _
  have hpre : (N.realizationIso hη).precomp (leftFibrationInfinityBaseChange k) =
      diagramIsoCongr hT hA (P.realizationIso hP) := by
    have hn := jointRealizationIso_precompose N (leftFibrationBaseChangeEnriched k) hη
    exact eq_of_heq ((diagramIsoCongr_heq hT hA (P.realizationIso hP)).trans
      ((heq_of_eq hn).trans (diagramIsoCongr_heq hT.symm hA.symm
        ((N.realizationIso hη).precomp (leftFibrationInfinityBaseChange k))))).symm
  rw [overPreJoint_iso, overPreJoint_iso, hpre]
  rw [relativeSectionBaseChangeRealizationIso_normalized k T,
    relativeSectionBaseChangeRealizationIso_normalized k A]
  calc
    _ = diagramIsoCongr hT rfl (BCT.realizationIso hBCT ≪≫ M.realizationIso hηk) := by
      rw [diagramIsoCongr_trans hT rfl rfl]
      simp only [diagramIsoCongr, eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl]
      rfl
    _ = diagramIsoCongr hT rfl (P.realizationIso hP ≪≫ BCA.realizationIso hBCA) :=
      congrArg (diagramIsoCongr hT rfl) hraw
    _ = _ := by rw [diagramIsoCongr_trans hT hA rfl]
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
