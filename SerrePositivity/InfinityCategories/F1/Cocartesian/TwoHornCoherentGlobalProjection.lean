module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoHornFaceTriangle
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.IsoRightTransport

/-!
概要：補正ホーン比較の大域同型の共有境界像は、面側が指定した像そのもの。
方針：補正 path の大域三角形への貼合せと、厳密な終点表示変更の消去を使う。
規約：面・ホーン双方の指定同型を保持する。
使われ方：coherent な境界比較の大域同型を厳密 pullback 上で貼る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable (j : Fin 2) (p q : CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "σ" => Iso.hom (stdSimplex.isoNerve 2)
local notation "τ" => stdSimplex.δ (1 : Fin 3) ≫ σ
local notation "R" => cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom
  (cocartesianFiniteHornOver 2 1)
local notation "N" => cocartesianTwoHornSharedNativeRestriction p q
local notation "T" => cocartesianTwoHornSharedTargetRestriction p q
local notation "H" => cocartesianTwoHornNativeTargetComparison p q
local notation "U" => cocartesianTwoHornCoherentComparison j p q
local notation "V" => cocartesianOneBoundaryHomComparison j τ p q

/-- 補正大域作用の共有境界の始点は、同じ直接共有境界作用。 -/
lemma cocartesianTwoHornCoherentGlobalIso_shared_source :
    (R ≫ U) ≫ T = R ≫ (N ≫ V) :=
  (Category.assoc _ _ _).trans
    (congrArg (fun f ↦ R ≫ f) (cocartesianTwoHornCoherentComparison_comm j p q))

/-- 同じ指定三角形による、終点表示変更を含む共有境界像の回収。 -/
lemma cocartesianTwoHornCoherentGlobalIso_shared_heq_transport :
    HEq ((cocartesianTwoHornCoherentComparison_originalIso j p q).postcomp T)
      (cocartesianTwoHornFaceInducedOriginalIso j p q ≪≫
        (cocartesianTwoHornSharedTargetOriginalIso p q).symm) := by
  exact (cocartesianTwoHornCoherentHomCorrection j p q).globalComposite_postcomp_heq R
    (cocartesianTwoHornNativeTargetComparison_originalIso p q)
    ((cocartesianTwoHornFaceCoherenceIso j p q).precomp R)
    ((cocartesianTwoHornNativeTargetComparison_originalIso p q).postcomp T)
    (cocartesianTwoHornFaceInducedOriginalIso j p q ≪≫
      (cocartesianTwoHornSharedTargetOriginalIso p q).symm)
    (cocartesianTwoHornCoherentGlobalIso_shared_source j p q)
    (Category.assoc R H T) rfl HEq.rfl HEq.rfl
    (cocartesianTwoHornFaceCoherenceIso_triangle j p q)

/-- 同じ共有境界像は、面側の大域同型から指定した値そのもの。 -/
lemma cocartesianTwoHornCoherentGlobalIso_shared_heq :
    HEq ((cocartesianTwoHornCoherentComparison_originalIso j p q).postcomp T)
      (cocartesianOneBoundaryFaceInducedOriginalIso j τ p q) := by
  have h := cocartesianTwoHornCoherentGlobalIso_shared_heq_transport j p q
  have hc : HEq
      (cocartesianTwoHornFaceInducedOriginalIso j p q ≪≫
        (cocartesianTwoHornSharedTargetOriginalIso p q).symm)
      (cocartesianTwoHornFaceInducedOriginalIso j p q) := by
    have ht : cocartesianTwoHornOriginalTargetAction p q ≫ T =
        cocartesianTwoHornSharedOriginalTargetAction p q := by
      rw [cocartesianTwoHornOriginalTargetAction, Category.assoc,
        cocartesianTwoHornSharedTargetRestriction_original]
      rfl
    unfold cocartesianTwoHornSharedTargetOriginalIso
    exact iso_trans_eqToIso_heq _
      (congrArg (fun f ↦ SSet.HomotopyCategory.mk (functorVertex f)) ht.symm)
  have hd : HEq (cocartesianTwoHornFaceInducedOriginalIso j p q)
      (cocartesianOneBoundaryFaceInducedOriginalIso j τ p q) := by
    dsimp only [cocartesianTwoHornFaceInducedOriginalIso, id]
    exact F2.functorIsoOfEq_heq _ _ _
  exact h.trans (hc.trans hd)

end SerrePositivity.InfinityCategories
