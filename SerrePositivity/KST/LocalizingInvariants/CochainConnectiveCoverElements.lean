module

public import SerrePositivity.KST.LocalizingInvariants.CochainConnectiveLift
public import SerrePositivity.DifferentialGraded.Complexes.Cells

/-!
概要：smart 非正次数切断への、負次数の任意元と非正次数の閉元の実持ち上げ。
方針：既存の disk と sphere の射を、非正次数複体からの一意な持ち上げで切断へ移す。
規約：ホモロジー類で元を置き換えない。使われ方：roof 分母の次数全射性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CochainComplex HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (K : Complex R)

lemma cochainTruncLE_lift_element (n : ℤ) (hn : n < 0) (x : K.X n) :
    ∃ y : (K.truncLE 0).X n, (K.ιTruncLE 0).f n y = x := by
  have : (complexDisk R n).IsStrictlyLE 0 := by
    apply (CochainComplex.isStrictlyLE_iff _ 0).2
    intro j hj
    exact isZero_double_X _ _ j (by omega) (by omega)
  let f := (complexDiskHomEquiv R K n).symm x
  let g := ConnectiveLift.lift f
  refine ⟨complexDiskHomEquiv R (K.truncLE 0) n g, ?_⟩
  calc
    _ = complexDiskHomEquiv R K n (g ≫ K.ιTruncLE 0) :=
      (complexDiskHomEquiv_naturality R n g (K.ιTruncLE 0)).symm
    _ = complexDiskHomEquiv R K n f := by rw [ConnectiveLift.lift_inclusion]
    _ = x := (complexDiskHomEquiv R K n).apply_symm_apply x

lemma cochainTruncLE_lift_cycle (n : ℤ) (hn : n ≤ 0) (x : complexCycles R K n) :
    ∃ y : (K.truncLE 0).X n, (K.ιTruncLE 0).f n y = x.val := by
  have : (complexSphere R n).IsStrictlyLE 0 := by
    apply (CochainComplex.isStrictlyLE_iff _ 0).2
    intro j hj
    exact isZero_single_obj_X (.up ℤ) n (𝟙_ (ModuleCat R)) j (by omega)
  let f := complexSphereMap R n x
  let g := ConnectiveLift.lift f
  refine ⟨(complexSphereCycle R n g).val, ?_⟩
  calc
    _ = (complexSphereCycle R n (g ≫ K.ιTruncLE 0)).val := rfl
    _ = (complexSphereCycle R n f).val := by rw [ConnectiveLift.lift_inclusion]
    _ = x.val := congrArg Subtype.val ((complexSphereHomEquiv R K n).apply_symm_apply x)

end SerrePositivity.KST.LocalizingInvariants
