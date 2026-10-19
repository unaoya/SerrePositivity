module
public import SerrePositivity.InfinityCategories.Derived.DGModuleVertexTriangles
public import SerrePositivity.InfinityCategories.Stable.StableHoTriangulated

/-! # 加群の対象条件と実 loop・全整数シフト

概要：K(D) の三角的対象条件は通常の h の全整数シフトでも保たれる。
方針：正シフトは実 cofiber、負シフトは零加群からの射の標準 fiber と loop の比較で得る。
規約：二つのシフトを定義的に同一視しない。使われ方：実安定閉包の対象条件の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : ObjectProperty (ModuleHomotopyCategory A D))
variable [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]

/-- K(D) の三角的対象条件は通常の h の負一回シフトでも保たれる。 -/
lemma dgModuleHoProperty_shift_neg_one {a : hoFunctor.obj (dgModuleNerve A D)}
    (ha : dgModuleHoProperty A D P a) : dgModuleHoProperty A D P (a⟦(-1 : ℤ)⟧) := by
  obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective a
  obtain ⟨M, rfl⟩ := Simplex.vertexEquiv.symm.surjective x
  let f : moduleZero A D ⟶ ForgetEnrichment.of (Complex A) M := 0
  let s : LoopSquare (X := dgModuleNerve A D) (Simplex.vertex M) := {
    toZeroTriangle := dgModuleFiberZeroTriangle A D f
    target_eq := dgModuleFiberSquare_vertex11 A D f
    other_zero := by
      change IsZeroVertex (squareVertex (dgModuleFiberSquare A D f) 1 0)
      rw [dgModuleFiberSquare_vertex10]
      exact dgModuleNerveZeroVertex_isZero A D
    isPullback := dgModuleFiberSquare_isPullback A D f }
  have hs : dgModuleHoProperty A D P (SSet.HomotopyCategory.mk s.vertex) := by
    change dgModuleHoProperty A D P
      (SSet.HomotopyCategory.mk (squareVertex (dgModuleFiberSquare A D f) 0 0))
    rw [dgModuleFiberSquare_vertex00]
    exact dgModuleHomotopyProperty_fiber A D P f
      (dgModuleHomotopyProperty_zero A D P) ha
  exact (dgModuleHoProperty A D P).prop_of_iso
    (((shiftNegOneLoopIso (dgModuleNerve A D)).app _ ≪≫ s.loopFunctorObjIso).symm) hs

section IntegerShift
variable {C : Type*} [Category* C] [HasShift C ℤ] (Q : ObjectProperty C)
  [Q.IsClosedUnderIsomorphisms]

private lemma integerShift_mem
    (hpos : ∀ a, Q a → Q (a⟦(1 : ℤ)⟧)) (hneg : ∀ a, Q a → Q (a⟦(-1 : ℤ)⟧))
    (n : ℤ) {a : C} (ha : Q a) : Q (a⟦n⟧) := by
  induction n using Int.induction_on with
  | zero => exact Q.prop_of_iso ((shiftFunctorZero C ℤ).app a).symm ha
  | succ n ih => exact Q.prop_of_iso ((shiftFunctorAdd C (n : ℤ) 1).app a).symm (hpos _ ih)
  | pred n ih =>
    exact Q.prop_of_iso
      ((shiftFunctorAdd' C (-(n : ℤ)) (-1) (-(n : ℤ) - 1) (by omega)).app a).symm (hneg _ ih)
end IntegerShift

/-- 通常の h 上の加群対象条件は全整数シフトで閉じる。 -/
instance dgModuleHoProperty_isStableUnderShift :
    (dgModuleHoProperty A D P).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun _ ha => integerShift_mem (dgModuleHoProperty A D P)
    (fun _ h => triangulatedClosed_shift_one _ h)
    (fun _ h => dgModuleHoProperty_shift_neg_one A D P h) n ha⟩

/-- K(D) の対象条件は通常の h の実三角構造に対しても三角的。 -/
instance dgModuleHoProperty_isTriangulated : (dgModuleHoProperty A D P).IsTriangulated where
  toIsTriangulatedClosed₂ := ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃

end SerrePositivity.InfinityCategories
