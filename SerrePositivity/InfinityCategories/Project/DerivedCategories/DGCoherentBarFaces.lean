module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarGraded
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentDiagramTopHom
/-!
概要：coherent bar の面と切断を元の全単体ラベルで記述する。
方針：元の単体写像を評価し、始点を保つ面の加群の厳密な等号を示す。
規約：単体ラベルと端点輸送を省略せず、余極限性はここでは主張しない。
使われ方：bar の面微分と prefix 微分の同時構成。
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

def dgCoherentBarFace {n : ℕ} (s : I _⦋n + 1⦌) (i : Fin (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I := ⟨n, I.δ i s⟩

lemma dgCoherentBarSource_face_succ {n : ℕ} (s : I _⦋n + 1⦌) (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F (dgCoherentBarFace s i.succ) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, s⟩ := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource dgCoherentBarFace
  congr 1
  change I.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op
    (I.map (SimplexCategory.δ i.succ).op s) = _
  have hc : SimplexCategory.const ⦋0⦌ ⦋n⦌ 0 ≫ SimplexCategory.δ i.succ =
      SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0 := by
    rw [SimplexCategory.const_comp]
    congr 1
  have h := ConcreteCategory.congr_hom
    (I.map_comp (SimplexCategory.δ i.succ).op (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op) s
  simpa only [← op_comp, hc, types_comp_apply] using h.symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
