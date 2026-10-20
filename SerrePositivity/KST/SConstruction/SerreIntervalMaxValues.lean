module
public import SerrePositivity.KST.SConstruction.SerreIntervalDegrees
public import SerrePositivity.KST.SConstruction.SerreIntervalCounit

/-! # max connection の元の全生成元での作用
概要：元の二端点と辺における max connection の作用と、右端点の法則を示す。
方針：Hom 値の lift と同じ収縮の値を回収し、区間の元の生成元で射を判定する。
規約：元の単位比較射を保持する。使われ方：connection の結合・Serre 対角保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の零左端点における全斉次成分は、第二因子そのもの。 -/
lemma serreIntervalMax_zero_apply (q : ℤ) (y : (serreInterval A).X q) :
    (serreIntervalMax A).f q
      (ιTensorObj (serreInterval A) (serreInterval A) 0 q q (zero_add q)
        ((cycleFromUnit _ (serreIntervalZero A)).val ⊗ₜ[A] y)) = y := by
  rw [serreIntervalMax_apply]
  have h := congrArg (fun f => (cycleFromUnit _ f).val) (serreIntervalMaxCurried_zero A)
  change (serreIntervalMaxCurried A).f 0 (cycleFromUnit _ (serreIntervalZero A)).val =
    (cycleFromUnit _ (identity (serreInterval A))).val at h
  rw [h]
  simp only [identity, cycleFromUnit_unitFromCycle, Cochain.ofHom_v]
  rfl

/-- 元の一左端点における全斉次成分は、元の一端点への定数射。 -/
lemma serreIntervalMax_one_apply (q : ℤ) (y : (serreInterval A).X q) :
    (serreIntervalMax A).f q
      (ιTensorObj (serreInterval A) (serreInterval A) 0 q q (zero_add q)
        ((cycleFromUnit _ (serreIntervalOne A)).val ⊗ₜ[A] y)) =
      (serreIntervalAugmentation A ≫ serreIntervalOne A).f q y := by
  rw [serreIntervalMax_apply]
  have h := congrArg (fun f => (cycleFromUnit _ f).val) (serreIntervalMaxCurried_one A)
  change (serreIntervalMaxCurried A).f 0 (cycleFromUnit _ (serreIntervalOne A)).val =
    (cycleFromUnit _ (closedMap A (serreIntervalAugmentation A ≫ serreIntervalOne A))).val at h
  rw [closedMap_cycle] at h
  rw [h, Cochain.ofHom_v]

/-- 元の左の辺における全斉次成分は、元の同じ収縮の値。 -/
lemma serreIntervalMax_edge_apply (q n : ℤ) (hn : -1 + q = n)
    (y : (serreInterval A).X q) :
    (serreIntervalMax A).f n
      (ιTensorObj (serreInterval A) (serreInterval A) (-1) q n hn
        (serreIntervalEdge A ⊗ₜ[A] y)) =
      (serreIntervalContraction A).v q n (by omega) y := by
  rw [serreIntervalMax_apply, serreIntervalMaxCurried_edge]

/-- 元の辺と零右端点の max は、同じ辺。 -/
lemma serreIntervalMax_edge_zero :
    (serreIntervalMax A).f (-1)
      (ιTensorObj (serreInterval A) (serreInterval A) (-1) 0 (-1) (by omega)
        (serreIntervalEdge A ⊗ₜ[A] (cycleFromUnit _ (serreIntervalZero A)).val)) =
      serreIntervalEdge A := by
  rw [serreIntervalMax_edge_apply, serreIntervalContraction_zero]

/-- 元の辺と一右端点の max は零。 -/
lemma serreIntervalMax_edge_one :
    (serreIntervalMax A).f (-1)
      (ιTensorObj (serreInterval A) (serreInterval A) (-1) 0 (-1) (by omega)
        (serreIntervalEdge A ⊗ₜ[A] (cycleFromUnit _ (serreIntervalOne A)).val)) = 0 := by
  rw [serreIntervalMax_edge_apply, serreIntervalContraction_one]

/-- 元の二つの辺の max は零。 -/
lemma serreIntervalMax_edge_edge :
    (serreIntervalMax A).f (-2)
      (ιTensorObj (serreInterval A) (serreInterval A) (-1) (-1) (-2) (by omega)
        (serreIntervalEdge A ⊗ₜ[A] serreIntervalEdge A)) = 0 := by
  rw [serreIntervalMax_edge_apply, serreIntervalContraction_edge]

/-- 元の零右端点と max connection は、元の右単位則を満たす。 -/
lemma serreIntervalMax_zero_right :
    (ρ_ (serreInterval A)).inv ≫ serreInterval A ◁ serreIntervalZero A ≫
      serreIntervalMax A = 𝟙 _ := by
  apply serreInterval_hom_ext A
  · apply (unitCycleEquiv _).injective
    apply Subtype.ext
    change (serreIntervalMax A).f 0 ((serreInterval A ◁ serreIntervalZero A).f 0
      ((ρ_ (serreInterval A)).inv.f 0 (cycleFromUnit _ (serreIntervalZero A)).val)) = _
    rw [complexRightUnitor_inv_apply, SerrePositivity.DifferentialGraded.whiskerLeft_apply]
    exact serreIntervalMax_zero_apply A 0 _
  · change (serreIntervalMax A).f (-1) ((serreInterval A ◁ serreIntervalZero A).f (-1)
      ((ρ_ (serreInterval A)).inv.f (-1) (serreIntervalEdge A))) = serreIntervalEdge A
    rw [complexRightUnitor_inv_apply, SerrePositivity.DifferentialGraded.whiskerLeft_apply]
    exact serreIntervalMax_edge_zero A

/-- 元の一右端点と max connection は、同じ一端点への定数射を回収する。 -/
lemma serreIntervalMax_one_right :
    (ρ_ (serreInterval A)).inv ≫ serreInterval A ◁ serreIntervalOne A ≫
      serreIntervalMax A = serreIntervalAugmentation A ≫ serreIntervalOne A := by
  apply serreInterval_hom_ext A
  · apply (unitCycleEquiv _).injective
    apply Subtype.ext
    change (serreIntervalMax A).f 0 ((serreInterval A ◁ serreIntervalOne A).f 0
        ((ρ_ (serreInterval A)).inv.f 0 (cycleFromUnit _ (serreIntervalZero A)).val)) =
      (serreIntervalOne A).f 0 ((serreIntervalAugmentation A).f 0
        (cycleFromUnit _ (serreIntervalZero A)).val)
    rw [complexRightUnitor_inv_apply, SerrePositivity.DifferentialGraded.whiskerLeft_apply,
      serreIntervalAugmentation_zero_value]
    exact serreIntervalMax_zero_apply A 0 _
  · change (serreIntervalMax A).f (-1) ((serreInterval A ◁ serreIntervalOne A).f (-1)
        ((ρ_ (serreInterval A)).inv.f (-1) (serreIntervalEdge A))) =
      (serreIntervalOne A).f (-1) ((serreIntervalAugmentation A).f (-1) (serreIntervalEdge A))
    rw [complexRightUnitor_inv_apply, SerrePositivity.DifferentialGraded.whiskerLeft_apply,
      serreIntervalAugmentation_edge,
      map_zero]
    exact serreIntervalMax_edge_one A

end SerrePositivity.KST.SConstruction
