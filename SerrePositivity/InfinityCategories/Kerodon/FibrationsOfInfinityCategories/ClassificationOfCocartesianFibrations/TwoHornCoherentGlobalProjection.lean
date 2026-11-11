module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoHornFaceTriangle
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.IsoRightTransport

/-!
概要：補正ホーン比較の大域同型の共有境界像は、面側が指定した像そのもの。
方針：補正 path の大域三角形への貼合せと、厳密な終点表示変更の消去を使う。
規約：面・ホーン双方の指定同型を保持する。
使われ方：coherent な境界比較の大域同型を厳密 pullback 上で貼る。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
variable (j : Fin 2) (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "σ" => Iso.hom (stdSimplex.isoNerve 2)
local notation "τ" => stdSimplex.δ (1 : Fin 3) ≫ σ
local notation "R" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFiniteHornOver 2 1)
local notation "N" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornSharedNativeRestriction p q
local notation "T" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornSharedTargetRestriction p q
local notation "H" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornNativeTargetComparison p q
local notation "U" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoHornCoherentCorrection.cocartesianTwoHornCoherentComparison j p q
local notation "V" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryHomComparison j τ p q

/-- 補正大域作用の共有境界の始点は、同じ直接共有境界作用。 -/
lemma cocartesianTwoHornCoherentGlobalIso_shared_source :
    (R ≫ U) ≫ T = R ≫ (N ≫ V) :=
  (Category.assoc _ _ _).trans
    (congrArg (fun f ↦ R ≫ f) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoHornCoherentCorrection.cocartesianTwoHornCoherentComparison_comm j p q))

/-- 同じ指定三角形による、終点表示変更を含む共有境界像の回収。 -/
lemma cocartesianTwoHornCoherentGlobalIso_shared_heq_transport :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoHornCoherentCorrection.cocartesianTwoHornCoherentComparison_originalIso j p q).postcomp T)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoHornFaceCoherence.cocartesianTwoHornFaceInducedOriginalIso j p q ≪≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornSharedTargetOriginalIso p q).symm) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoHornCoherentCorrection.cocartesianTwoHornCoherentHomCorrection j p q).globalComposite_postcomp_heq R
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornNativeTargetComparison_originalIso p q)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoHornFaceCoherence.cocartesianTwoHornFaceCoherenceIso j p q).precomp R)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornNativeTargetComparison_originalIso p q).postcomp T)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoHornFaceCoherence.cocartesianTwoHornFaceInducedOriginalIso j p q ≪≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornSharedTargetOriginalIso p q).symm)
    (cocartesianTwoHornCoherentGlobalIso_shared_source j p q)
    (Category.assoc R H T) rfl HEq.rfl HEq.rfl
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornFaceCoherenceIso_triangle j p q)

/-- 同じ共有境界像は、面側の大域同型から指定した値そのもの。 -/
lemma cocartesianTwoHornCoherentGlobalIso_shared_heq :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoHornCoherentCorrection.cocartesianTwoHornCoherentComparison_originalIso j p q).postcomp T)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryFaceInducedOriginalIso j τ p q) := by
  have h := cocartesianTwoHornCoherentGlobalIso_shared_heq_transport j p q
  have hc : HEq
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoHornFaceCoherence.cocartesianTwoHornFaceInducedOriginalIso j p q ≪≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornSharedTargetOriginalIso p q).symm)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoHornFaceCoherence.cocartesianTwoHornFaceInducedOriginalIso j p q) := by
    have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornOriginalTargetAction p q ≫ T =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornSharedOriginalTargetAction p q := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornOriginalTargetAction, Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornSharedTargetRestriction_original]
      rfl
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornSharedTargetOriginalIso
    exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.iso_trans_eqToIso_heq _
      (congrArg (fun f ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) ht.symm)
  have hd : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoHornFaceCoherence.cocartesianTwoHornFaceInducedOriginalIso j p q)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryFaceInducedOriginalIso j τ p q) := by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoHornFaceCoherence.cocartesianTwoHornFaceInducedOriginalIso, id]
    exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _
  exact h.trans (hc.trans hd)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
