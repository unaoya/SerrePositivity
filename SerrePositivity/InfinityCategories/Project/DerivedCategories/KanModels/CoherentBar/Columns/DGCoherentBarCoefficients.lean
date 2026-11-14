module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CoherentBar.Faces.DGCoherentBarFaces
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CoherentBar.Faces.DGCoherentBarCuts
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleHomEndpointTransport
/-!
概要：元の coherent 図式の面と prefix の斉次成分を、bar 直和上の次数一成分に置く。
方針：同じ単体ラベルの shift ブロックと、元の余積包含を合成する。
規約：全パラメーターと端点輸送を保持する。MC 方程式はここでは仮定も主張もしない。
使われ方：D-8 c2 の実 bar 微分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

def dgCoherentBarFaceBlock {n : ℕ} (s : I _⦋n + 1⦌) (i : Fin (n + 1)) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n + 1, s⟩))
      (ForgetEnrichment.to (Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace s i.succ)))).X 1 :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomTargetTransport R D
    (_root_.SerrePositivity.DifferentialGraded.shiftModule ((n + 1 : ℕ) : ℤ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, s⟩))
    (_root_.SerrePositivity.DifferentialGraded.shiftModule (n : ℤ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, s⟩))
    (_root_.SerrePositivity.DifferentialGraded.shiftModule (n : ℤ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace s i.succ)))
    (congrArg (_root_.SerrePositivity.DifferentialGraded.shiftModule (n : ℤ)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource_face_succ R D F s i)).symm 1
    (_root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D ((n + 1 : ℕ) : ℤ) (n : ℤ)
      (M := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, s⟩)
      (N := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, s⟩)
      (unitElement R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, s⟩)).val (by omega))).val

lemma dgCoherentBarPrefix_target {n : ℕ} (s : I _⦋n⦌) (k : ℕ) (h : k + 1 ≤ n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex F
      (I.map (SimplexCategory.const ⦋0⦌ ⦋k + 1⦌ (Fin.last (k + 1))).op
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix s (k + 1) h).2) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail s (k + 1) h) := by
  have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex_map F (m := k + 1) (n := n)
    (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixOrder n (k + 1) h)) s (Fin.last (k + 1))
  have hz : (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixOrder n (k + 1) h)).toOrderHom
      (Fin.last (k + 1)) = (⟨k + 1, by omega⟩ : Fin (n + 1)) := rfl
  rw [hz] at hv
  exact hv.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource_tail R D F s (k + 1) h).symm

def dgCoherentBarPrefixHom {n : ℕ} (s : I _⦋n⦌) (k : ℕ) (h : k + 1 ≤ n) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, s⟩)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail s (k + 1) h))).X (-(k : ℤ)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := R) (D := _root_.SerrePositivity.DifferentialGraded.RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource_prefix R D F s (k + 1) h)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix_target R D F s k h) rfl
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix s (k + 1) h).2)

def dgCoherentBarPrefixBlock {n : ℕ} (s : I _⦋n⦌) (k : ℕ) (h : k + 1 ≤ n) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
      (ForgetEnrichment.to (Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail s (k + 1) h)))).X 1 :=
  _root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D (n : ℤ) ((n - (k + 1) : ℕ) : ℤ)
    (dgCoherentBarPrefixHom R D F s k h) (by omega)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
