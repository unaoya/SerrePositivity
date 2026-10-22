module

public import SerrePositivity.InfinityCategories.F1.CocartesianTwoHornCoherentCorrection
public import SerrePositivity.InfinityCategories.F1.PathCorrectedSquareGlobalTriangle

/-!
概要：面側から指定した自然性の逆向き三角形を、補正同型の合成向きへ移す。
方針：同じ指定三角形の後端を消去し、逆同型で前端を消去する。
規約：既存の指定同型の値を保持する。
使われ方：補正ホーン比較の大域同型の共有境界像。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories
variable (j : Fin 2) (p q : CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "R" => cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom
  (cocartesianFiniteHornOver 2 1)
local notation "T" => cocartesianTwoHornSharedTargetRestriction p q

/-- 補正同型の共有境界像と大域同型を合成すると、面側が指定した同じ像になる。 -/
lemma cocartesianTwoHornFaceCoherenceIso_triangle :
    IsoTriangleCommutes
      ((cocartesianTwoHornFaceCoherenceIso j p q).precomp R)
      ((cocartesianTwoHornNativeTargetComparison_originalIso p q).postcomp T)
      (cocartesianTwoHornFaceInducedOriginalIso j p q ≪≫
        (cocartesianTwoHornSharedTargetOriginalIso p q).symm) := by
  have hi := cocartesianTwoHornFaceCoherenceReverseIso_original j p q
  have hp := congrArg (fun e ↦ e ≪≫ (cocartesianTwoHornSharedTargetOriginalIso p q).symm) hi
  have hp' :
      (cocartesianTwoHornFaceCoherenceReverseIso j p q).precomp R ≪≫
        (cocartesianTwoHornFaceInducedOriginalIso j p q ≪≫
          (cocartesianTwoHornSharedTargetOriginalIso p q).symm) =
      (cocartesianTwoHornNativeTargetComparison_originalIso p q).postcomp T := by
    simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using hp
  unfold IsoTriangleCommutes
  rw [cocartesianTwoHornFaceCoherenceIso, F2.functorIso_precomp_symm, ← hp']
  simp only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]

end SerrePositivity.InfinityCategories
