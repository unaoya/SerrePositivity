module

public import SerrePositivity.FieldTheory.SubfieldSpanIntersection
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-! # 部分体の合成と共通の線形包

有限拡大内の部分体の合成を、より小さい共通の底体での生成族の線形包として扱う。
独立性の係数制限はMathlibの一般的なスカラー変換の定理を使う。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable {K L τ : Type*} [Field K] [Field L] [Algebra K L]

/-- 体上の独立性を、同じ係数作用を持つ埋め込みの像上へ移す。 -/
theorem linearIndependent_fieldRange (v : τ → L) (hv : LinearIndependent K v) :
    LinearIndependent (algebraMap K L).fieldRange v := by
  let e := (algebraMap K L).rangeRestrictFieldEquiv
  have h := hv.map_of_injective_injectiveₛ e.symm (AddMonoidHom.id L) e.symm.injective
    Function.injective_id (fun r m ↦ ?_)
  · exact h
  · have hr := congrArg (fun c : (algebraMap K L).fieldRange ↦ (c : L))
      (e.apply_symm_apply r)
    change algebraMap K L (e.symm r) = (r : L) at hr
    simp only [Algebra.smul_def, AddMonoidHom.id_apply, Subfield.algebraMap_ofSubfield]
    change algebraMap K L (e.symm r) * m = (r : L) * m
    rw [hr]

/-- 部分体の包含に沿って独立性を係数制限する。 -/
theorem linearIndependent_subfield_of_le {E S : Subfield L} (hES : E ≤ S)
    (v : τ → L) (hv : LinearIndependent S v) : LinearIndependent E v := by
  exact hv.map_of_injective_injectiveₛ (Subfield.inclusion hES) (AddMonoidHom.id L)
    (RingHom.injective (Subfield.inclusion hES)) Function.injective_id (fun _ _ ↦ rfl)

/-- 部分体の合成を、共通の小さい底体での生成族の線形包として計算する。
有限性は合成が部分代数と中間体のどちらでも同じになるために使う。 -/
theorem mem_subfield_sup_iff_mem_span
    (F E S : Subfield L) [Module.Finite E L] (hFE : F ≤ E)
    (v : τ → L) (hspan : (S : Set L) = (Submodule.span F (Set.range v) : Set L)) (z : L) :
    z ∈ E ⊔ S ↔ z ∈ Submodule.span E (Set.range v) := by
  let : Algebra F E := (Subfield.inclusion hFE).toAlgebra
  let : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq' (R := F) (S := E) (A := L) rfl
  have heq : (IntermediateField.adjoin E (S : Set L)).toSubfield = E ⊔ S := by
    rw [IntermediateField.adjoin_toSubfield]
    have hr : Set.range (algebraMap E L) = (E : Set L) := by
      ext y
      constructor
      · rintro ⟨c, rfl⟩; exact c.property
      · intro hy; exact ⟨⟨y, hy⟩, rfl⟩
    rw [hr, Subfield.closure_union, Subfield.closure_eq, Subfield.closure_eq]
  rw [← heq]
  change z ∈ (IntermediateField.adjoin E (S : Set L)).toSubalgebra.toSubmodule ↔ _
  rw [IntermediateField.adjoin_toSubalgebra]
  change z ∈ (Algebra.adjoin E (S.toSubmonoid : Set L)).toSubmodule ↔ _
  rw [S.toSubmonoid.adjoin_eq_span_of_eq_span F E hspan]

end SerrePositivity
