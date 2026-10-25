module
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarCoefficients
public import SerrePositivity.DifferentialGraded.Module.ShiftBlockLinear
public import SerrePositivity.InfinityCategories.DGNerve.HomHEqAlgebra
/-!
概要：bar の始点を保つ面の shift ブロックは閉次数一要素である。
方針：元の始点加群の等号に沿って戻し、単位ブロックの微分消滅を使う。
規約：元の面ラベル・加群・輸送を保持し、他の境界項の消滅は主張しない。
使われ方：正次元 bar 列の MC 展開から面の内部微分項を消す。
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

lemma dgCoherentBarFaceBlock_heq {n : ℕ} (s : I _⦋n + 1⦌) (i : Fin (n + 1)) :
    HEq (dgCoherentBarFaceBlock R D F s i)
      (moduleHomShiftBlock R D ((n + 1 : ℕ) : ℤ) (n : ℤ)
        (M := dgCoherentBarSource R D F ⟨n + 1, s⟩)
        (N := dgCoherentBarSource R D F ⟨n + 1, s⟩)
        (unitElement R (dgCoherentBarSource R D F ⟨n + 1, s⟩)).val
        (by omega : ((n + 1 : ℕ) : ℤ) + 0 - (n : ℤ) = 1)) := by
  exact (dgModuleHomTargetTransport R D
    (shiftModule ((n + 1 : ℕ) : ℤ) (dgCoherentBarSource R D F ⟨n + 1, s⟩))
    (shiftModule (n : ℤ) (dgCoherentBarSource R D F ⟨n + 1, s⟩))
    (shiftModule (n : ℤ) (dgCoherentBarSource R D F (dgCoherentBarFace s i.succ)))
    (congrArg (shiftModule (n : ℤ)) (dgCoherentBarSource_face_succ R D F s i)).symm 1
    (moduleHomShiftBlock R D ((n + 1 : ℕ) : ℤ) (n : ℤ)
      (M := dgCoherentBarSource R D F ⟨n + 1, s⟩)
      (N := dgCoherentBarSource R D F ⟨n + 1, s⟩)
      (unitElement R (dgCoherentBarSource R D F ⟨n + 1, s⟩)).val (by omega))).property

lemma dgCoherentBarFaceBlock_d {n : ℕ} (s : I _⦋n + 1⦌) (i : Fin (n + 1)) :
    (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n + 1, s⟩))
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarFamily R D F (dgCoherentBarFace s i.succ)))).d 1 2
      (dgCoherentBarFaceBlock R D F s i) = 0 := by
  let M := dgCoherentBarSource R D F ⟨n + 1, s⟩
  let N := dgCoherentBarSource R D F (dgCoherentBarFace s i.succ)
  have hy : shiftModule (n : ℤ) N = shiftModule (n : ℤ) M :=
    congrArg (shiftModule (n : ℤ)) (dgCoherentBarSource_face_succ R D F s i)
  have hf := dgCoherentBarFaceBlock_heq R D F s i
  have hd := gradedHom_differential_heq (A := R) (D := RightModule R D)
    (x := shiftModule ((n + 1 : ℕ) : ℤ) M) (y := shiftModule (n : ℤ) N)
    (x' := shiftModule ((n + 1 : ℕ) : ℤ) M) (y' := shiftModule (n : ℤ) M)
    rfl hy rfl _ _ hf
  have hb := moduleHomShiftBlock_unit_d R D ((n + 1 : ℕ) : ℤ) (n : ℤ) M 1
    (by omega)
  have hz := gradedHom_zero_heq (A := R) (D := RightModule R D)
    (x := shiftModule ((n + 1 : ℕ) : ℤ) M) (y := shiftModule (n : ℤ) N)
    (x' := shiftModule ((n + 1 : ℕ) : ℤ) M) (y' := shiftModule (n : ℤ) M)
    (k := (1 : ℤ) + 1) (l := (1 : ℤ) + 1) rfl hy rfl
  exact eq_of_heq ((hd.trans (heq_of_eq hb)).trans hz.symm)

end SerrePositivity.InfinityCategories
