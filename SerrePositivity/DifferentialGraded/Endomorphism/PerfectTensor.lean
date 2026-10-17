module
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedTensorTriangles
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedGenerators
public import SerrePositivity.DifferentialGraded.Endomorphism.PerfectShiftTriangles

/-! # 実際の再構成導来tensorの主Perfへの制限 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)

local instance : (endomorphismDerivedTensor A D E.val).CommShift ℤ :=
  endomorphismDerivedTensorCommShift A D E.val E.property.1
local instance : (endomorphismDerivedTensor A D E.val).IsTriangulated :=
  endomorphismDerivedTensorIsTriangulated A D E.val E.property.1

/-- 指定対象がperfectなら、再構成導来tensorは全perfect End加群をPerf_Sへ送る。 -/
lemma perfectEndomorphismTensor_obj_perfect
    {N : DerivedModuleCategory A (EndomorphismObject E.val)}
    (hN : modulePerfect A (EndomorphismObject E.val) N) :
    modulePerfectOver A D S ((endomorphismDerivedTensor A D E.val).obj N) := by
  let P := (modulePerfectOver A D S).inverseImage (endomorphismDerivedTensor A D E.val)
  have : P.IsTriangulated := by dsimp [P]; infer_instance
  have : P.IsClosedUnderIsomorphisms := by dsimp [P]; infer_instance
  have : P.IsStableUnderRetracts :=
    ⟨fun h hY => (modulePerfectOver A D S).prop_of_retract
      (h.map (endomorphismDerivedTensor A D E.val)) hY⟩
  apply ((modulePerfect_le_iff_generators A (EndomorphismObject E.val) P).2 ?_) N hN
  intro b
  cases b
  change modulePerfectOver A D S _
  exact (modulePerfectOver A D S).prop_of_iso
    (endomorphismDerivedTensor_regularIso A D E.val).symm E.property.2

/-- 既存の主導来tensorそのものを主Perfへ制限する。thick生成仮定は不要。 -/
def perfectEndomorphismTensorToPerfect :
    PerfectModuleCategory A (EndomorphismObject E.val) ⥤ PerfectModuleCategoryOver A D S :=
  (modulePerfectOver A D S).lift
    (perfectModuleInclusion A (EndomorphismObject E.val) Set.univ ⋙
      endomorphismDerivedTensor A D E.val)
    (fun N => perfectEndomorphismTensor_obj_perfect A D S E N.property)

@[instance_reducible]
def perfectEndomorphismTensorCommShift :
    (perfectEndomorphismTensorToPerfect A D S E).CommShift ℤ := by
  unfold perfectEndomorphismTensorToPerfect
  infer_instance

local instance : (perfectEndomorphismTensorToPerfect A D S E).CommShift ℤ :=
  perfectEndomorphismTensorCommShift A D S E

lemma perfectEndomorphismTensorIsTriangulated :
    (perfectEndomorphismTensorToPerfect A D S E).IsTriangulated := by
  unfold perfectEndomorphismTensorToPerfect
  infer_instance

def perfectEndomorphismTensorInclusionIso :
    perfectEndomorphismTensorToPerfect A D S E ⋙ perfectModuleInclusion A D S ≅
      perfectModuleInclusion A (EndomorphismObject E.val) Set.univ ⋙
        endomorphismDerivedTensor A D E.val :=
  (modulePerfectOver A D S).liftCompιIso _ _

lemma perfectEndomorphismTensorInclusionIso_commShift :
    NatTrans.CommShift (perfectEndomorphismTensorInclusionIso A D S E).hom ℤ := by
  unfold perfectEndomorphismTensorInclusionIso
  infer_instance

end SerrePositivity.DifferentialGraded
