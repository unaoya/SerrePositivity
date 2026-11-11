module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarCoefficients
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarFaceBlock_heq {n : ℕ} (s : I _⦋n + 1⦌) (i : Fin (n + 1)) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceBlock R D F s i)
      (_root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D ((n + 1 : ℕ) : ℤ) (n : ℤ)
        (M := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, s⟩)
        (N := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, s⟩)
        (unitElement R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, s⟩)).val
        (by omega : ((n + 1 : ℕ) : ℤ) + 0 - (n : ℤ) = 1)) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomTargetTransport R D
    (_root_.SerrePositivity.DifferentialGraded.shiftModule ((n + 1 : ℕ) : ℤ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, s⟩))
    (_root_.SerrePositivity.DifferentialGraded.shiftModule (n : ℤ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, s⟩))
    (_root_.SerrePositivity.DifferentialGraded.shiftModule (n : ℤ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace s i.succ)))
    (congrArg (_root_.SerrePositivity.DifferentialGraded.shiftModule (n : ℤ)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource_face_succ R D F s i)).symm 1
    (_root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D ((n + 1 : ℕ) : ℤ) (n : ℤ)
      (M := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, s⟩)
      (N := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, s⟩)
      (unitElement R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, s⟩)).val (by omega))).property

lemma dgCoherentBarFaceBlock_d {n : ℕ} (s : I _⦋n + 1⦌) (i : Fin (n + 1)) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n + 1, s⟩))
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace s i.succ)))).d 1 2
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceBlock R D F s i) = 0 := by
  let M := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, s⟩
  let N := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace s i.succ)
  have hy : _root_.SerrePositivity.DifferentialGraded.shiftModule (n : ℤ) N = _root_.SerrePositivity.DifferentialGraded.shiftModule (n : ℤ) M :=
    congrArg (shiftModule (n : ℤ)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource_face_succ R D F s i)
  have hf := dgCoherentBarFaceBlock_heq R D F s i
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_differential_heq (A := R) (D := RightModule R D)
    (x := _root_.SerrePositivity.DifferentialGraded.shiftModule ((n + 1 : ℕ) : ℤ) M) (y := _root_.SerrePositivity.DifferentialGraded.shiftModule (n : ℤ) N)
    (x' := _root_.SerrePositivity.DifferentialGraded.shiftModule ((n + 1 : ℕ) : ℤ) M) (y' := _root_.SerrePositivity.DifferentialGraded.shiftModule (n : ℤ) M)
    rfl hy rfl _ _ hf
  have hb := _root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock_unit_d R D ((n + 1 : ℕ) : ℤ) (n : ℤ) M 1
    (by omega)
  have hz := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := R) (D := RightModule R D)
    (x := _root_.SerrePositivity.DifferentialGraded.shiftModule ((n + 1 : ℕ) : ℤ) M) (y := _root_.SerrePositivity.DifferentialGraded.shiftModule (n : ℤ) N)
    (x' := _root_.SerrePositivity.DifferentialGraded.shiftModule ((n + 1 : ℕ) : ℤ) M) (y' := _root_.SerrePositivity.DifferentialGraded.shiftModule (n : ℤ) M)
    (k := (1 : ℤ) + 1) (l := (1 : ℤ) + 1) rfl hy rfl
  exact eq_of_heq ((hd.trans (heq_of_eq hb)).trans hz.symm)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
