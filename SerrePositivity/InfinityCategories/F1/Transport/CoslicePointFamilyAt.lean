module
public import SerrePositivity.InfinityCategories.F1.Transport.CoslicePointComparison

/-! # 既存の coslice 点族を指定点で評価し、同じ恒等点から元の全写像を回収する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
  (b : B _⦋0⦌)

/-- 既存の全 fiber 点族の、指定された同じ一つの実点での値。 -/
def coslicePointFamilyAt (v : (vertexFiber p b) _⦋0⦌) :
    sliceUnder (yonedaEquiv.symm b) ⟶ E :=
  lift (𝟙 _) (SSet.const v) ≫ leftFibrationCoslicePointFamily p b

/-- 同じ点族の値は元の底を厳密に固定する。 -/
theorem coslicePointFamilyAt_projection (v : (vertexFiber p b) _⦋0⦌) :
    coslicePointFamilyAt p b v ≫ p = sliceUnderProjection (yonedaEquiv.symm b) := by
  rw [coslicePointFamilyAt, Category.assoc, leftFibrationCoslicePointFamily_projection,
    ← Category.assoc, lift_fst, Category.id_comp]

/-- 恒等錐での同じ実評価は、元の指定 fiber 点そのもの。 -/
theorem coslicePointFamilyAt_identity (v : (vertexFiber p b) _⦋0⦌) :
    (coslicePointFamilyAt p b v).app (Opposite.op ⦋0⦌) (cosliceIdentityCone b) = v.val := by
  have he : (SSet.const (cosliceIdentityCone b) : (Δ[0] : SSet.{u}) ⟶ _) ≫
      lift (𝟙 _) (SSet.const v) =
      (SSet.const v : (Δ[0] : SSet.{u}) ⟶ _) ≫
        lift (SSet.const (cosliceIdentityCone b)) (𝟙 (vertexFiber p b)) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, Category.comp_id, SSet.comp_const]
    · simp only [Category.assoc, lift_snd, Category.comp_id, SSet.comp_const]
  have hf : (SSet.const (cosliceIdentityCone b) : (Δ[0] : SSet.{u}) ⟶ _) ≫
      coslicePointFamilyAt p b v = SSet.const v.val := by
    change (SSet.const (cosliceIdentityCone b) ≫ lift (𝟙 _) (SSet.const v)) ≫
      leftFibrationCoslicePointFamily p b = _
    rw [he, Category.assoc, leftFibrationCoslicePointFamily_identity, SSet.const_comp]
    rfl
  have hh := congrArg SSet.yonedaEquiv hf
  simpa only [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_const] using hh

/-- 元の coslice 写像と同じ恒等錐の値から作った点族の写像は、全写像空間内で同型。 -/
def coslicePointFamilyAt_recoveryIso
    (f : sliceUnder (yonedaEquiv.symm b) ⟶ E)
    (hf : f ≫ p = sliceUnderProjection (yonedaEquiv.symm b)) :
    FunctorIso (coslicePointFamilyAt p b
      ((leftFibrationCoslicePointEvaluate p b).app (Opposite.op ⦋0⦌)
        (relativeFunctorVertex p _ f hf))) f := by
  apply coslicePointEvaluation_functorIso p b (coslicePointFamilyAt_projection p b _) hf
  apply eqToIso
  apply congrArg HomotopyCategory.mk
  apply Subtype.ext
  exact (coslicePointEvaluation_vertex_val p b (coslicePointFamilyAt_projection p b _)).trans
    (coslicePointFamilyAt_identity p b _)

end SerrePositivity.KST.Fibration
