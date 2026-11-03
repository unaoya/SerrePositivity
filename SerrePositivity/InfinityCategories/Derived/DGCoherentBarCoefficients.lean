module
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarFaces
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarCuts
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
public import SerrePositivity.InfinityCategories.Derived.DGModuleHomEndpointTransport
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

def dgCoherentBarFaceBlock {n : ℕ} (s : I _⦋n + 1⦌) (i : Fin (n + 1)) :
    (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n + 1, s⟩))
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarFamily R D F (dgCoherentBarFace s i.succ)))).X 1 :=
  (dgModuleHomTargetTransport R D
    (shiftModule ((n + 1 : ℕ) : ℤ) (dgCoherentBarSource R D F ⟨n + 1, s⟩))
    (shiftModule (n : ℤ) (dgCoherentBarSource R D F ⟨n + 1, s⟩))
    (shiftModule (n : ℤ) (dgCoherentBarSource R D F (dgCoherentBarFace s i.succ)))
    (congrArg (shiftModule (n : ℤ)) (dgCoherentBarSource_face_succ R D F s i)).symm 1
    (moduleHomShiftBlock R D ((n + 1 : ℕ) : ℤ) (n : ℤ)
      (M := dgCoherentBarSource R D F ⟨n + 1, s⟩)
      (N := dgCoherentBarSource R D F ⟨n + 1, s⟩)
      (unitElement R (dgCoherentBarSource R D F ⟨n + 1, s⟩)).val (by omega))).val

lemma dgCoherentBarPrefix_target {n : ℕ} (s : I _⦋n⦌) (k : ℕ) (h : k + 1 ≤ n) :
    coherentDiagramVertex F
      (I.map (SimplexCategory.const ⦋0⦌ ⦋k + 1⦌ (Fin.last (k + 1))).op
        (dgCoherentBarPrefix s (k + 1) h).2) =
      dgCoherentBarSource R D F (dgCoherentBarTail s (k + 1) h) := by
  have hv := coherentDiagramVertex_map F (m := k + 1) (n := n)
    (SimplexCategory.mkHom (dgCoherentBarPrefixOrder n (k + 1) h)) s (Fin.last (k + 1))
  have hz : (SimplexCategory.mkHom (dgCoherentBarPrefixOrder n (k + 1) h)).toOrderHom
      (Fin.last (k + 1)) = (⟨k + 1, by omega⟩ : Fin (n + 1)) := rfl
  rw [hz] at hv
  exact hv.trans (dgCoherentBarSource_tail R D F s (k + 1) h).symm

def dgCoherentBarPrefixHom {n : ℕ} (s : I _⦋n⦌) (k : ℕ) (h : k + 1 ≤ n) :
    (moduleHom R D (dgCoherentBarSource R D F ⟨n, s⟩)
      (dgCoherentBarSource R D F (dgCoherentBarTail s (k + 1) h))).X (-(k : ℤ)) :=
  gradedHomTransport (A := R) (D := RightModule R D) (dgCoherentBarSource_prefix R D F s (k + 1) h)
    (dgCoherentBarPrefix_target R D F s k h) rfl
    (coherentDiagramTop F (dgCoherentBarPrefix s (k + 1) h).2)

def dgCoherentBarPrefixBlock {n : ℕ} (s : I _⦋n⦌) (k : ℕ) (h : k + 1 ≤ n) :
    (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarFamily R D F (dgCoherentBarTail s (k + 1) h)))).X 1 :=
  moduleHomShiftBlock R D (n : ℤ) ((n - (k + 1) : ℕ) : ℤ)
    (dgCoherentBarPrefixHom R D F s k h) (by omega)

end SerrePositivity.InfinityCategories
