module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointCofiberComparison
public import SerrePositivity.KST.Spectra.SphereMappingComponents

/-!
概要：相対 cofiber 上の元の Kan 随伴比較を、球面の同じ代表が与える正次数の類へ移す。
方針：実際の降下射の成分の一致へ球面を前合成し、既存の球面成分比較を適用する。
規約：全列の写像類の一致は主張しない。使われ方：段座標の球面代表による検出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A B : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence) (j : B ⟶ A) [Mono j.right] (hzero : j ≫ φ = 0)

/-- 同じ cofiber への球面を用いると、元の二つの座標は同じ正次数の類を表す。 -/
lemma kanAdjointCofiberComparison_sphereClass (n r : ℕ)
    (s : PointedSimplicialSet.sphere.{u} (r + 1) ⟶ pointedCofiber j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (SphereSimplex.equiv (kanAdjointParameterTarget X Y n) (r + 1)
      (s ≫ kanAdjointCofiberComparison X Y φ j hzero ≫
        pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (SphereSimplex.equiv (kanAdjointParameterTarget X Y n) (r + 1)
      (s ≫ kanAdjointCofiberInput X Y φ j hzero ≫ kanAdjointParameterLeft X Y n)) := by
  let parameterTargetKan : KanComplex (kanAdjointParameterTarget X Y n).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  apply (SphereSimplex.class_eq_iff_components (kanAdjointParameterTarget X Y n) r _ _).2
  exact PointedMapping.componentOf_comp_left
    (kanAdjointCofiberComparison_evaluation_component X Y φ j hzero n) s

/-- BF 模型の元の射影座標でも、同じ球面代表が同じ正次数の類を与える。 -/
lemma kanAdjointCofiberBFComparison_projected_sphereClass (n r : ℕ)
    (s : PointedSimplicialSet.sphere.{u} (r + 1) ⟶ pointedCofiber j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (SphereSimplex.equiv (kanAdjointParameterTarget X Y n) (r + 1)
      (s ≫ (kanAdjointCofiberBFComparison X Y φ j hzero ≫
        pointedEvaluation X (OmegaSpectrum.signedLoopModel Y).toKanSequence n) ≫
        PointedObject.basedHomMap (X.level n).space
          ((OmegaSpectrum.signedLoopProjection Y).app n))) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (SphereSimplex.equiv (kanAdjointParameterTarget X Y n) (r + 1)
      (s ≫ kanAdjointCofiberInput X Y φ j hzero ≫ kanAdjointParameterLeft X Y n)) := by
  have h := congrArg (fun f ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk
    (SphereSimplex.equiv (kanAdjointParameterTarget X Y n) (r + 1) (s ≫ f)))
      (kanAdjointCofiberBFComparison_projected_evaluation X Y φ j hzero n)
  simp only [Category.assoc] at h ⊢
  exact h.trans (kanAdjointCofiberComparison_sphereClass X Y φ j hzero n r s)

end SerrePositivity.KST.Spectra.RawSpectrumMapping
