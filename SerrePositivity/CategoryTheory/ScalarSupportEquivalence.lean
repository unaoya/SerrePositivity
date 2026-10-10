module

public import SerrePositivity.CategoryTheory.ScalarSupport
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-! # 線形三角同値の支持部分圏への制限 -/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits

variable {R : Type*} [CommRing R] {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
  (E : C ≌ D) [E.functor.Linear R] [E.functor.Additive] {e : ℕ} (z : Fin e → R)

lemma scalarSupported_equivalence_iff (X : C) :
    scalarSupported z (E.functor.obj X) ↔ scalarSupported z X := by
  constructor
  · rintro ⟨v, hv, h⟩
    refine ⟨v, hv, fun j ↦ E.functor.map_injective ?_⟩
    simpa only [Functor.map_smul, E.functor.map_id, E.functor.map_zero] using h j
  · exact scalarSupported_map z E.functor X

/-- 線形同値は同じパラメータで支持される部分圏の同値を誘導する。 -/
noncomputable def scalarSupportEquivalence :
    (scalarSupported (C := C) z).FullSubcategory ≌ (scalarSupported (C := D) z).FullSubcategory :=
  E.congrFullSubcategory (by ext X; exact scalarSupported_equivalence_iff E z X)

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C n).Linear R] [Pretriangulated C]
  [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Linear R] [Pretriangulated D]
  [E.functor.CommShift ℤ] [E.functor.IsTriangulated]

noncomputable instance scalarSupportEquivalence_functor_commShift :
    (scalarSupportEquivalence E z).functor.CommShift ℤ := by
  dsimp [scalarSupportEquivalence, CategoryTheory.Equivalence.congrFullSubcategory]
  infer_instance

instance scalarSupportEquivalence_functor_isTriangulated :
    (scalarSupportEquivalence E z).functor.IsTriangulated := by
  let P := scalarSupported (C := C) z
  let Q := scalarSupported (C := D) z
  exact (Functor.isTriangulated_iff_comp_right
    (Q.liftCompιIso (P.ι ⋙ E.functor) _)).mpr inferInstance

noncomputable instance scalarSupportEquivalence_inverse_commShift :
    (scalarSupportEquivalence E z).inverse.CommShift ℤ :=
  (scalarSupportEquivalence E z).commShiftInverse ℤ

instance scalarSupportEquivalence_commShift : (scalarSupportEquivalence E z).CommShift ℤ :=
  (scalarSupportEquivalence E z).commShift_of_functor ℤ

instance scalarSupportEquivalence_isTriangulated : (scalarSupportEquivalence E z).IsTriangulated :=
  CategoryTheory.Equivalence.IsTriangulated.mk' _ inferInstance

end SerrePositivity
