module
public import SerrePositivity.DifferentialGraded.Endomorphism.HomComparisonCone

/-! # 指定生成対象のthick閉包上の全Hom擬同型

K(D)内の有限なshift・三角形・retract閉包を明示し、U13のenhancementの
thick生成仮定から全Hom比較を取り出す。本質的全射は別の証明義務。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated HomologicalComplex
open scoped ZeroObject
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 指定対象Eを含む、K(D)内の有限操作によるthick閉包。 -/
inductive endomorphismThickClosure (E : RightModule A D) :
    ObjectProperty (ModuleHomotopyCategory A D)
  | generator : endomorphismThickClosure E
      ((moduleToHomotopy A D).obj (ForgetEnrichment.of (Complex A) E))
  | zero : endomorphismThickClosure E 0
  | shift {X} (s : ℤ) : endomorphismThickClosure E X → endomorphismThickClosure E (X⟦s⟧)
  | triangle (T : Triangle (ModuleHomotopyCategory A D)) (hT : T ∈ distTriang _) :
      endomorphismThickClosure E T.obj₁ → endomorphismThickClosure E T.obj₂ →
        endomorphismThickClosure E T.obj₃
  | retract {X Y} (a : Retract X Y) :
      endomorphismThickClosure E Y → endomorphismThickClosure E X

variable (E : RightModule A D)

instance endomorphismThickClosureStableUnderRetracts :
    (endomorphismThickClosure A D E).IsStableUnderRetracts where
  of_retract a h := endomorphismThickClosure.retract a h

instance endomorphismThickClosureStableUnderShift :
    (endomorphismThickClosure A D E).IsStableUnderShift ℤ where
  isStableUnderShiftBy s := ⟨fun _ h => endomorphismThickClosure.shift s h⟩

instance endomorphismThickClosureContainsZero :
    (endomorphismThickClosure A D E).ContainsZero :=
  ⟨⟨0, Limits.isZero_zero _, endomorphismThickClosure.zero⟩⟩

instance endomorphismThickClosureTriangulatedClosed₃ :
    (endomorphismThickClosure A D E).IsTriangulatedClosed₃ :=
  ObjectProperty.IsTriangulatedClosed₃.mk' (fun T hT h₁ h₂ =>
    endomorphismThickClosure.triangle T hT h₁ h₂)

instance endomorphismThickClosureTriangulatedClosed₂ :
    (endomorphismThickClosure A D E).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃

instance endomorphismThickClosureIsTriangulated :
    (endomorphismThickClosure A D E).IsTriangulated where

/-- 上の有限操作閉包はEを含む任意のthick部分圏に含まれる。 -/
lemma endomorphismThickClosure_le (P : ObjectProperty (ModuleHomotopyCategory A D))
    [P.IsTriangulated] [P.IsStableUnderRetracts]
    (hE : P ((moduleToHomotopy A D).obj (ForgetEnrichment.of (Complex A) E))) :
    endomorphismThickClosure A D E ≤ P := by
  intro X hX
  induction hX with
  | generator => exact hE
  | zero => exact P.prop_zero
  | shift s _ ih => exact P.le_shift s _ ih
  | triangle T hT _ _ ih₁ ih₂ =>
      have h := P.ext_of_isTriangulatedClosed₃' T hT ih₁ ih₂
      simpa only [ObjectProperty.isoClosure_eq_self] using h
  | retract a _ ih => exact P.prop_of_retract a ih

lemma endomorphismHomComparison_of_thick {M : ModuleCategory A D}
    (hM : endomorphismThickClosure A D E ((moduleToHomotopy A D).obj M))
    (T : ModuleCategory A D) : QuasiIso ((endomorphismModuleHom A D E).map M T) :=
  endomorphismThickClosure_le A D E (endomorphismHomComparisonLocus A D E)
    (endomorphismHomComparisonLocus_generator A D E) _ hM T

/-- U13の全指定perfect対象がEから有限thick操作で生成される、という仮定。 -/
def endomorphismThickGeneratesPerfect (S : Set D) (E : PerfectDGModuleOver A D S) : Prop :=
  ∀ M : PerfectDGModuleOver A D S, endomorphismThickClosure A D E.val
    ((moduleToHomotopy A D).obj (ForgetEnrichment.of (Complex A) M.val))

/-- thick生成の下での全Hom擬同型。H⁰の本質的全射とは独立の結論。 -/
lemma perfectEndomorphismModuleHom_homQuasiIso (S : Set D) (E : PerfectDGModuleOver A D S)
    (hgen : endomorphismThickGeneratesPerfect A D S E) :
    HomQuasiIso (perfectEndomorphismModuleHom A D S E) := by
  intro M N
  have h := endomorphismHomComparison_of_thick A D E.val (hgen M)
    (ForgetEnrichment.of (Complex A) N.val)
  change QuasiIso (𝟙 _ ≫ (endomorphismModuleHom A D E.val).map M.val N.val)
  rw [Category.id_comp]
  exact h

end SerrePositivity.DifferentialGraded
