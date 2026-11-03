module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.DegeneracyOperators
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
public import SerrePositivity.InfinityCategories.DGNerve.HomHEqAlgebra
/-!
概要：始点を保つ単体写像を、実 bar の係数族の閉斉次ブロックとして扱う。
方針：同じ始点加群のシフト単位ブロックを、元の単体ラベルへ輸送する。
規約：射の向きと全次数を保持し、次数の異なるブロックを通常の加群射にしない。
使われ方：面・退化の合成を同じ単位ブロックへ戻し、正規化の係数を比較する。
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

lemma dgCoherentBarSource_based_map {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (hf : f.toOrderHom 0 = 0) (s : I _⦋n⦌) :
    dgCoherentBarSource R D F ⟨m, I.map f.op s⟩ =
      dgCoherentBarSource R D F ⟨n, s⟩ := by
  have h := coherentDiagramVertex_map F f s 0
  simpa only [dgCoherentBarSource, hf] using h

def dgCoherentBarBasedBlock {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (hf : f.toOrderHom 0 = 0) (s : I _⦋n⦌) :
    GradedHom R
      (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨m, I.map f.op s⟩))
      ((n : ℤ) - (m : ℤ)) :=
  gradedHomTransport rfl
    (congrArg (shiftModule (m : ℤ)) (dgCoherentBarSource_based_map R D F f hf s)).symm rfl
    (moduleHomShiftBlock R D (n : ℤ) (m : ℤ)
      (unitElement R (dgCoherentBarSource R D F ⟨n, s⟩)).val (by omega))

lemma dgCoherentBarBasedBlock_heq {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (hf : f.toOrderHom 0 = 0) (s : I _⦋n⦌) :
    HEq (dgCoherentBarBasedBlock R D F f hf s)
      (moduleHomShiftBlock R D (n : ℤ) (m : ℤ)
        (unitElement R (dgCoherentBarSource R D F ⟨n, s⟩)).val
        (by omega : (n : ℤ) + 0 - (m : ℤ) = (n : ℤ) - (m : ℤ))) :=
  gradedHomTransport_heq _ _ _ _

lemma dgCoherentBarBasedBlock_d {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (hf : f.toOrderHom 0 = 0) (s : I _⦋n⦌) :
    differential R (dgCoherentBarBasedBlock R D F f hf s) = 0 := by
  let M := dgCoherentBarSource R D F ⟨n, s⟩
  have ht := congrArg (shiftModule (m : ℤ))
    (dgCoherentBarSource_based_map R D F f hf s)
  have h := gradedHom_differential_heq (A := R) (D := RightModule R D)
    rfl ht rfl _ _ (dgCoherentBarBasedBlock_heq R D F f hf s)
  have hz := moduleHomShiftBlock_unit_d R D (n : ℤ) (m : ℤ) M
    ((n : ℤ) - (m : ℤ)) (by omega)
  have hzero := gradedHom_zero_heq (A := R) (D := RightModule R D)
    (x := shiftModule (n : ℤ) M)
    (y := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨m, I.map f.op s⟩))
    (x' := shiftModule (n : ℤ) M) (y' := shiftModule (m : ℤ) M)
    (k := (n : ℤ) - (m : ℤ) + 1) (l := (n : ℤ) - (m : ℤ) + 1)
    rfl ht rfl
  exact eq_of_heq (h.trans (heq_of_eq hz) |>.trans hzero.symm)

end SerrePositivity.InfinityCategories
