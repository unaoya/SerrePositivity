module

public import SerrePositivity.KST.Spectra.TracedSignedLoopUnit
public import SerrePositivity.KST.Spectra.FiberOmegaSpectrum
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointStructureIntervals

/-!
概要：全 Hom の Kan 随伴構造区間と、トレース付き BF 単位に同じ区間を使う。
方針：標的で固定した単位構造区間と延長区間を、内部 Hom の作用と普遍評価で移す。
規約：成分から区間を選び直さない。使われ方：非零境界を保つ比較の共通構造入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence)

/-- 係数逆区間は、同じ単位構造区間への内部 Hom の作用そのもの。 -/
lemma kanAdjointCoefficientReversePath_unit (n : ℕ) :
    kanAdjointCoefficientReversePath X Y n =
      PointedMapping.VerticalPath.basedIhomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        (OmegaSpectrum.signedLoopUnitStructurePath Y n) := rfl

/-- 全 Hom の構造区間も同じ単位区間を元の懸垂評価へ前合成した同じ辺。 -/
lemma kanAdjointParameterStructureInterval_unit_path (n : ℕ) :
    (kanAdjointParameterStructureInterval X Y φ n).path =
      ((PointedMapping.VerticalPath.basedIhomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        (OmegaSpectrum.signedLoopUnitStructurePath Y n)).pre
          (kanAdjointStructureInput X Y φ n)).path := rfl

/-- 元の Kan 随伴座標から、トレース付き単位の同じ全 Hom の段評価への実区間。 -/
def kanAdjointTracedUnitEvaluationInterval (n : ℕ) :
    PointedMapping.VerticalPath (PointedObject.toPoint (kanAdjointParameterTarget X Y n))
      (φ ≫ kanAdjointParameterLeft X Y n)
      (φ ≫ pointedPost X (OmegaSpectrum.sequenceHom (OmegaSpectrum.tracedSignedLoopUnit Y)) ≫
        pointedPost X (OmegaSpectrum.signedLoopProjection Y) ≫
        pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n) := by
  let P := (PointedMapping.VerticalPath.basedIhomMap (X.level n).space
    (OmegaSpectrum.tracedSignedLoopUnitComparison Y n)).pre
      (φ ≫ pointedEvaluation X Y.toKanSequence n)
  have hs : φ ≫ kanAdjointParameterLeft X Y n =
      (φ ≫ pointedEvaluation X Y.toKanSequence n) ≫
        (ihom (X.level n).space).map (KanSequence.kanAdjoint Y.toKanSequence n) := by
    exact (Category.assoc _ _ _).symm
  have ht : (φ ≫ pointedPost X
      (OmegaSpectrum.sequenceHom (OmegaSpectrum.tracedSignedLoopUnit Y)) ≫
      pointedPost X (OmegaSpectrum.signedLoopProjection Y) ≫
      pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n) =
    (φ ≫ pointedEvaluation X Y.toKanSequence n) ≫
      (ihom (X.level n).space).map
        ((OmegaSpectrum.tracedSignedLoopUnit Y).app n ≫
          (OmegaSpectrum.signedLoopProjection Y).app n) := by
    simp only [Category.assoc, pointedPost_evaluation, pointedPost_evaluation_assoc]
    rw [Functor.map_comp]
    rfl
  exact P.changeEndpoints hs ht

/-- 同じ延長区間の内部 Hom 像と評価だけで、段比較の辺そのものを計算する。 -/
lemma kanAdjointTracedUnitEvaluationInterval_path (n : ℕ) :
    (kanAdjointTracedUnitEvaluationInterval X Y φ n).path =
      ((PointedMapping.VerticalPath.basedIhomMap (X.level n).space
        (OmegaSpectrum.tracedSignedLoopUnitComparison Y n)).pre
          (φ ≫ pointedEvaluation X Y.toKanSequence n)).path := rfl

/-- 元の単位の同じ延長区間全体を評価した式。全 Hom パラメータでも区間を選び直さない。 -/
lemma kanAdjointTracedUnitEvaluationInterval_h (n : ℕ) :
    (kanAdjointTracedUnitEvaluationInterval X Y φ n).homotopy.h =
      (φ ≫ pointedEvaluation X Y.toKanSequence n).right ▷ (Δ[1] : SSet.{u}) ≫
        (PointedMapping.VerticalPath.basedIhomMap (X.level n).space
          (OmegaSpectrum.tracedSignedLoopUnitComparison Y n)).homotopy.h := by
  rw [kanAdjointTracedUnitEvaluationInterval,
    PointedMapping.VerticalPath.changeEndpoints_homotopy_h,
    PointedMapping.VerticalPath.pre_homotopy_h]

/-- 任意の非零部分パラメータでも、同じ元の延長区間への入力だけを制限する。 -/
lemma kanAdjointTracedUnitEvaluationInterval_boundary {B : PointedSimplicialSet.{u}}
    (j : B ⟶ A) (n : ℕ) :
    j.right ▷ (Δ[1] : SSet.{u}) ≫
      (kanAdjointTracedUnitEvaluationInterval X Y φ n).homotopy.h =
    ((j ≫ φ) ≫ pointedEvaluation X Y.toKanSequence n).right ▷ (Δ[1] : SSet.{u}) ≫
      (PointedMapping.VerticalPath.basedIhomMap (X.level n).space
        (OmegaSpectrum.tracedSignedLoopUnitComparison Y n)).homotopy.h := by
  rw [kanAdjointTracedUnitEvaluationInterval_h, ← comp_whiskerRight_assoc]
  rfl

end SerrePositivity.KST.Spectra.RawSpectrumMapping
