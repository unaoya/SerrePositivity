module
public import SerrePositivity.DifferentialGraded.Module.LeftEquivalence
public import SerrePositivity.DifferentialGraded.Module.QuasiIso

/-! # 左dg加群の指定objectwise quasiIso -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 既存左右同値による、Dᵒᵖ上の指定準同型クラスの逆像。 -/
def leftModuleQuasiIso : MorphismProperty (LeftModuleCategory A D) :=
  (moduleQuasiIso A Dᵒᵖ).inverseImage (leftModuleToRightOpposite A D)

lemma leftModuleQuasiIso_iff {L L' : LeftModuleCategory A D} (g : L ⟶ L') :
    leftModuleQuasiIso A D g ↔ ∀ x : D, QuasiIso ((leftModuleEvaluation A D x).map g) := by
  change (∀ x : Dᵒᵖ, QuasiIso ((moduleEvaluation A Dᵒᵖ x).map
    ((leftModuleToRightOpposite A D).map g))) ↔ _
  constructor
  · intro h x
    simpa only [leftModuleToRightOpposite_map_eval] using h (op x)
  · intro h x
    obtain ⟨x⟩ := x
    simpa only [leftModuleToRightOpposite_map_eval] using h x

instance leftModuleQuasiIsoIsMultiplicative : (leftModuleQuasiIso A D).IsMultiplicative := by
  dsimp [leftModuleQuasiIso]
  infer_instance

instance leftModuleQuasiIsoHasTwoOutOfThree :
    (leftModuleQuasiIso A D).HasTwoOutOfThreeProperty := by
  dsimp [leftModuleQuasiIso]
  infer_instance

instance leftModuleQuasiIsoStableUnderRetracts :
    (leftModuleQuasiIso A D).IsStableUnderRetracts := by
  dsimp [leftModuleQuasiIso]
  infer_instance

instance leftModuleQuasiIsoRespectsIso : (leftModuleQuasiIso A D).RespectsIso := by
  dsimp [leftModuleQuasiIso]
  infer_instance

end SerrePositivity.DifferentialGraded
