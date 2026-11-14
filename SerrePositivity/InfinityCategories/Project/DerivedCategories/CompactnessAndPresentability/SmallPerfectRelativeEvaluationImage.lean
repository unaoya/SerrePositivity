module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.SmallPerfectRelativeEvaluation
/-!
概要：小 Perf 評価核の主導来作用は、元の指定 S で生成する完全加群へ入る。
方針：指定 perfect 条件の逆像を取り、代表列から thick 生成の一般判定を使う。
規約：対象ごとの代表選択を作用関手へ混ぜない。全 Perf の Small 性は不要。
使われ方：D-18 の tria の対象を元の小代表系へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D] (S : Set D)
local notation "C" => SmallPerfectDGModuleOver R D S

lemma smallPerfectRelativeEvaluation_preservesPerfectOver
    {X : DerivedModuleCategory R (C)} (hX : modulePerfect R (C) X) :
    modulePerfectOver R D S ((Morita.kernelDerivedTensor R (C) D
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectRelativeEvaluationKernel R D S)).obj X) := by
  let T := Morita.kernelDerivedTensor R (C) D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectRelativeEvaluationKernel R D S)
  letI : T.CommShift ℤ := Morita.criterionPerfKernelCommShift R (C) D _
  letI : T.IsTriangulated := Morita.criterionPerfKernelIsTriangulated R (C) D _
  let P := (modulePerfectOver R D S).inverseImage T
  haveI : P.IsTriangulated := by dsimp [P]; infer_instance
  haveI : P.IsClosedUnderIsomorphisms := by dsimp [P]; infer_instance
  haveI : P.IsStableUnderRetracts :=
    ⟨fun r h => (modulePerfectOver R D S).prop_of_retract (r.map T) h⟩
  apply ((modulePerfect_le_iff_generators R (C) P).mpr ?_) X hX
  intro c
  exact (modulePerfectOver R D S).prop_of_iso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectRelativeEvaluation_representableIso R D S c).symm c.val.property.2

end SerrePositivity.InfinityCategories.Project.DerivedCategories
