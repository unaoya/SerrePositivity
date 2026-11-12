module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointParameterBFComparison
public import SerrePositivity.KST.Spectra.PointedComponentIsomorphism

/-!
概要：全パラメータで持ち上げた BF 比較の段座標を、元の signedLoopUnit の後合成と比較する。
方針：BF 射影後の成分を Kan 随伴へ照合し、元の Hom の射影の π 同型性で打ち消す。
規約：各段の全パラメータの比較。使われ方：元の BF 単位と普遍評価の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- BF 比較の段評価は、元の全 Hom の評価を元の BF 単位へ後合成した族と同じ成分。 -/
lemma kanAdjointParameterBFComparison_unit_component (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    PointedMapping.componentOf (kanAdjointParameterBFComparison X Y ≫
      pointedEvaluation X (OmegaSpectrum.signedLoopModel Y).toKanSequence n) =
    PointedMapping.componentOf (pointedEvaluation X Y.toKanSequence n ≫
      PointedObject.basedHomMap (X.level n).space ((OmegaSpectrum.signedLoopUnit Y).app n)) := by
  let q := (OmegaSpectrum.signedLoopProjection Y).app n
  let v := (OmegaSpectrum.signedLoopUnit Y).app n
  let sourceHomKan : KanComplex
      (PointedObject.basedHom (X.level n).space
        ((OmegaSpectrum.signedLoopModel Y).level n).space).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  let targetHomKan : KanComplex
      (PointedObject.basedHom (X.level n).space
        ((KanSequence.signedLoopTail Y.toKanSequence).level n).space).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  have hq : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism q.right :=
    KanSequence.replacementProjection_piIsomorphism (KanSequence.signedLoopTail Y.toKanSequence) n
  apply PointedMapping.componentOf_cancel_post_piIsomorphism
    (PointedObject.basedHomMap (X.level n).space q)
    (PointedMapping.post_piIsomorphism (X.level n).space q hq)
  have hr := PointedMapping.componentOf_comp_left
    (PointedMapping.componentOf_ihom_map (X.level n).space
      (OmegaSpectrum.signedLoopUnit_projection_component Y n))
    (pointedEvaluation X Y.toKanSequence n)
  have he : (pointedEvaluation X Y.toKanSequence n ≫
      PointedObject.basedHomMap (X.level n).space v) ≫
        PointedObject.basedHomMap (X.level n).space q =
      pointedEvaluation X Y.toKanSequence n ≫ (ihom (X.level n).space).map (v ≫ q) := by
    rw [Functor.map_comp, Category.assoc]
    rfl
  rw [he]
  exact (kanAdjointParameterBFComparison_projected_component X Y n).trans hr.symm

/-- 上の各段の比較を、元の全 Hom の基点を固定する実際のホモトピーで実現する。 -/
lemma kanAdjointParameterBFComparison_unit_homotopy (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    ∃ H : SSet.Homotopy (kanAdjointParameterBFComparison X Y ≫
        pointedEvaluation X (OmegaSpectrum.signedLoopModel Y).toKanSequence n).right
        (pointedEvaluation X Y.toKanSequence n ≫
          PointedObject.basedHomMap (X.level n).space
            ((OmegaSpectrum.signedLoopUnit Y).app n)).right,
      (pointedSpace X Y.toKanSequence).hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫
          (PointedObject.basedHom (X.level n).space
            ((OmegaSpectrum.signedLoopModel Y).level n).space).hom := by
  let coordinateKan : KanComplex
      (PointedObject.basedHom (X.level n).space
        ((OmegaSpectrum.signedLoopModel Y).level n).space).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  exact (PointedMapping.piZero_eq_iff_pointedHomotopy _ _).1
    (kanAdjointParameterBFComparison_unit_component X Y n)

end SerrePositivity.KST.Spectra.RawSpectrumMapping
