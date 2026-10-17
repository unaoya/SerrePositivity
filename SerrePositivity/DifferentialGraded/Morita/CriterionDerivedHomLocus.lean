module
public import SerrePositivity.DifferentialGraded.Morita.CriterionDerivedHomTriangles

/-! # 全shiftでのHom比較の全単射性が定める局所化帰納の対象クラス -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits Pretriangulated ZeroObject
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (T : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
  (X : DerivedModuleCategory A D)

/-- 固定した始域から全整数shiftへの実際のHom比較が全単射となる終域。 -/
def criterionDerivedHomTargetLocus : ObjectProperty (DerivedModuleCategory A D) :=
  fun Y => ∀ n : ℤ, Function.Bijective (fun f : X ⟶ Y⟦n⟧ => T.map f)

lemma criterionDerivedHomTargetLocus_shift {Y : DerivedModuleCategory A D}
    (hY : criterionDerivedHomTargetLocus A D E T X Y) (a : ℤ) :
    criterionDerivedHomTargetLocus A D E T X (Y⟦a⟧) := by
  intro b
  exact criterionDerivedHom_target_iso A D E T X
    ((shiftFunctorAdd _ a b).app Y).symm (hY (a + b))

instance criterionDerivedHomTargetLocusClosedIso :
    (criterionDerivedHomTargetLocus A D E T X).IsClosedUnderIsomorphisms where
  of_iso e hY n := criterionDerivedHom_target_iso A D E T X
    ((shiftFunctor _ n).mapIso e.symm) (hY n)

instance criterionDerivedHomTargetLocusShift :
    (criterionDerivedHomTargetLocus A D E T X).IsStableUnderShift ℤ where
  isStableUnderShiftBy a := ⟨fun _ hY => criterionDerivedHomTargetLocus_shift A D E T X hY a⟩

variable [T.CommShift ℤ] [T.IsTriangulated]

instance criterionDerivedHomTargetLocusClosedTriangle :
    (criterionDerivedHomTargetLocus A D E T X).IsTriangulatedClosed₃ := by
  apply ObjectProperty.IsTriangulatedClosed₃.mk'
  intro Δ hΔ h1 h2 n
  apply criterionDerivedHom_target_triangle A D E T X _
    (Triangle.shift_distinguished Δ hΔ n) (h1 n) (h2 n)
  · exact (criterionDerivedHomTargetLocus_shift A D E T X h1 n) 1
  · exact (criterionDerivedHomTargetLocus_shift A D E T X h2 n) 1

instance criterionDerivedHomTargetLocusTriangulated :
    (criterionDerivedHomTargetLocus A D E T X).IsTriangulated where
  exists_zero := ⟨0, isZero_zero _, fun n =>
    criterionDerivedHom_target_isZero A D E T X ((shiftFunctor _ n).map_isZero (isZero_zero _))⟩
  toIsTriangulatedClosed₂ := ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃

/-- 各compact生成元とそのcompactな像に対するHom比較の対象クラスは、余積で閉じる。 -/
lemma criterionDerivedHomTargetLocus_coproduct
    (hcop : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) T)
    (hX : moduleCompact A D X) (hTX : moduleCompact A E (T.obj X))
    (J : Type u) (F : J → DerivedModuleCategory A D)
    (hF : ∀ j, criterionDerivedHomTargetLocus A D E T X (F j)) :
    criterionDerivedHomTargetLocus A D E T X (∐ F) := by
  intro n
  let := hcop J
  apply criterionDerivedHom_target_iso A D E T X
    (PreservesCoproduct.iso (shiftFunctor _ n) F)
  exact criterionDerivedHom_coproduct_bijective A D E T (fun j => (F j)⟦n⟧) X
    hX hTX (fun j => hF j n)

end SerrePositivity.DifferentialGraded.Morita
