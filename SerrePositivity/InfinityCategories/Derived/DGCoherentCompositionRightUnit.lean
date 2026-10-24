module
public import SerrePositivity.InfinityCategories.Derived.DGCoherentCompositionUnitLaws
public import SerrePositivity.InfinityCategories.Derived.DGCompositionUnitCollapse
/-!
概要：coherent dg 合成の第二入力の恒等射を、全図式の退化として表示する。
方針：切替後の頂点を終点へ写す単調写像で Hom 比較を引き戻す。
規約：Small 仮定なしに全単体・全時刻と端点の等式輸送を保持する。
使われ方：D2 の単位合成三角形の全パラメーター付き退化表示。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded
open DGNerve DoldKanComparison SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

lemma dgCoherentCompositionObj_second_unit (x y : ClosedCategory A D) {n : ℕ}
    (t : Fin (n + 1) →o Fin 2) (i : Fin (n + 2)) :
    coherentHomComparisonObj x y (dgCompositionUnitCollapse t i) =
      coherentCompositionObj x y y t i := by
  induction i using Fin.lastCases with
  | last => simp [dgCompositionUnitCollapse_last, coherentHomComparisonObj_last,
      coherentCompositionObj_last]
  | cast i =>
    by_cases hi : t i = 0
    · simp [dgCompositionUnitCollapse_zero t i hi, coherentHomComparisonObj_cast,
        coherentCompositionObj_zero x y y t i hi]
    · simp [dgCompositionUnitCollapse_one t i hi, coherentHomComparisonObj_last,
        coherentCompositionObj_one x y y t i hi]

lemma dgStandardUnit_lift_comp_right {x y : D} {K : SSet.{u}}
    (h : K ⟶ standardHomSpace (R := A) (D := D) x y) :
    lift h (toUnit K ≫ standardUnitMap (R := A) (D := D) y) ≫
      eComp SSet (ForgetEnrichment.of (Complex A) x)
        (ForgetEnrichment.of (Complex A) y) (ForgetEnrichment.of (Complex A) y) = h := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  exact simplicialHom_comp_id_app (ForgetEnrichment.of (Complex A) x)
    (ForgetEnrichment.of (Complex A) y) _ (h.app _ a)

lemma dgCoherentHomComparisonHom_cast_cast {x y : D} {n : ℕ}
    (σ : StandardSimplex A x y n) (i j : Fin (n + 1)) :
    coherentHomComparisonHom (C := ClosedCategory A D)
      (X := ForgetEnrichment.of (Complex A) x) (Y := ForgetEnrichment.of (Complex A) y)
      σ i.castSucc j.castSucc ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentHomComparisonObj_cast (ForgetEnrichment.of (Complex A) x)
          (ForgetEnrichment.of (Complex A) y) i)
        (coherentHomComparisonObj_cast (ForgetEnrichment.of (Complex A) x)
          (ForgetEnrichment.of (Complex A) y) j)) =
      toUnit _ ≫ eId SSet (ForgetEnrichment.of (Complex A) x) := by
  simp -implicitDefEqProofs +instances [coherentHomComparisonHom, coherentHomComparisonObj]

lemma dgCoherentRightUnit_normalized {x y : D} {n : ℕ}
    (σ : StandardSimplex A x y n) (t : Fin (n + 1) →o Fin 2)
    (i j i' j' : Fin (n + 2)) (a b : ClosedCategory A D)
    (hi : dgCompositionUnitCollapse t i = i')
    (hj : dgCompositionUnitCollapse t j = j')
    (ha : coherentCompositionObj (ForgetEnrichment.of (Complex A) x)
      (ForgetEnrichment.of (Complex A) y) (ForgetEnrichment.of (Complex A) y) t i = a)
    (hb : coherentCompositionObj (ForgetEnrichment.of (Complex A) x)
      (ForgetEnrichment.of (Complex A) y) (ForgetEnrichment.of (Complex A) y) t j = b)
    (ha' : coherentHomComparisonObj (ForgetEnrichment.of (Complex A) x)
      (ForgetEnrichment.of (Complex A) y) i' = a)
    (hb' : coherentHomComparisonObj (ForgetEnrichment.of (Complex A) x)
      (ForgetEnrichment.of (Complex A) y) j' = b)
    (h : (SimplicialThickening.functor (dgCompositionUnitCollapse t).uliftMap).map
        (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up j⟩ ≫
      eqToHom (congrArg₂ (fun a b : Fin (n + 2) => SimplicialCategory.sHom
        (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up b⟩) hi hj) ≫
      coherentHomComparisonHom (C := ClosedCategory A D)
        (X := ForgetEnrichment.of (Complex A) x) (Y := ForgetEnrichment.of (Complex A) y) σ i' j' ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom ha' hb') =
      coherentCompositionHom (C := ClosedCategory A D)
        (X := ForgetEnrichment.of (Complex A) x) (Y := ForgetEnrichment.of (Complex A) y)
        (Z := ForgetEnrichment.of (Complex A) y) σ (standardUnit (R := A) (D := D) y n) t i j ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom ha hb)) :
    ((SimplicialThickening.functor (dgCompositionUnitCollapse t).uliftMap).map
      (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up j⟩ ≫
      coherentHomComparisonHom (C := ClosedCategory A D)
        (X := ForgetEnrichment.of (Complex A) x) (Y := ForgetEnrichment.of (Complex A) y)
        σ (dgCompositionUnitCollapse t i) (dgCompositionUnitCollapse t j)) ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (dgCoherentCompositionObj_second_unit A D _ _ t i)
        (dgCoherentCompositionObj_second_unit A D _ _ t j)) =
      coherentCompositionHom (C := ClosedCategory A D)
        (X := ForgetEnrichment.of (Complex A) x) (Y := ForgetEnrichment.of (Complex A) y)
        (Z := ForgetEnrichment.of (Complex A) y) σ (standardUnit (R := A) (D := D) y n) t i j := by
  apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom ha hb))).1
  simp only [Category.assoc, eqToHom_trans]
  change _ ≫ coherentHomComparisonHom (C := ClosedCategory A D)
      (X := ForgetEnrichment.of (Complex A) x) (Y := ForgetEnrichment.of (Complex A) y)
      σ (dgCompositionUnitCollapse t i) (dgCompositionUnitCollapse t j) ≫
    eqToHom (congrArg₂ SimplicialCategory.sHom
      ((congrArg (coherentHomComparisonObj (ForgetEnrichment.of (Complex A) x)
        (ForgetEnrichment.of (Complex A) y)) hi).trans ha')
      ((congrArg (coherentHomComparisonObj (ForgetEnrichment.of (Complex A) x)
        (ForgetEnrichment.of (Complex A) y)) hj).trans hb')) = _
  erw [coherentHomComparisonHom_transport (C := ClosedCategory A D)
    (X := ForgetEnrichment.of (Complex A) x) (Y := ForgetEnrichment.of (Complex A) y)
    σ hi hj ha' hb' ]
  simpa only [Category.assoc] using h

set_option maxHeartbeats 1200000 in
-- 全頂点対の分岐と端点輸送を一つの豊穣関手の等式へ束ねるため。
lemma dgCoherentCompositionSimplex_second_unit {x y : D} {n : ℕ}
    (σ : StandardSimplex A x y n) (t : Fin (n + 1) →o Fin 2) :
    (SimplicialThickening.functor (dgCompositionUnitCollapse t).uliftMap).comp SSet
      (coherentHomComparisonSimplex (C := ClosedCategory A D)
        (X := ForgetEnrichment.of (Complex A) x) (Y := ForgetEnrichment.of (Complex A) y) σ) =
    coherentCompositionSimplex (C := ClosedCategory A D)
      (X := ForgetEnrichment.of (Complex A) x) (Y := ForgetEnrichment.of (Complex A) y)
      (Z := ForgetEnrichment.of (Complex A) y)
      σ (standardUnit (R := A) (D := D) y n) t := by
  let X := ForgetEnrichment.of (Complex A) x
  let Y := ForgetEnrichment.of (Complex A) y
  apply EnrichedFunctor.ext SSet
    (fun i => dgCoherentCompositionObj_second_unit A D X Y t i.as.down)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  change (_ ≫ coherentHomComparisonHom (C := ClosedCategory A D) (X := X) (Y := Y)
    σ (dgCompositionUnitCollapse t i)
    (dgCompositionUnitCollapse t j)) ≫ eqToHom _ =
      coherentCompositionHom (C := ClosedCategory A D) (X := X) (Y := Y) (Z := Y)
        σ (standardUnit (R := A) (D := D) y n) t i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases
  case last.last =>
    apply dgCoherentRightUnit_normalized A D σ t _ _ _ _ Y Y
      (dgCompositionUnitCollapse_last t) (dgCompositionUnitCollapse_last t)
      (coherentCompositionObj_last X Y Y n t) (coherentCompositionObj_last X Y Y n t)
      (coherentHomComparisonObj_last X Y n) (coherentHomComparisonObj_last X Y n)
    erw [coherentHomComparisonHom_last_last,
        coherentCompositionHom_last_last]
    simp only [← Category.assoc, comp_toUnit]
  case last.cast j =>
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    have h := SimplicialThickening.Path.le (P.obj 0)
    change n + 1 ≤ j.val at h
    have hj := j.isLt
    omega
  case cast.last i =>
    by_cases hi : t i = 0
    · apply dgCoherentRightUnit_normalized A D σ t _ _ _ _ X Y
        (dgCompositionUnitCollapse_zero t i hi) (dgCompositionUnitCollapse_last t)
        (coherentCompositionObj_zero X Y Y t i hi) (coherentCompositionObj_last X Y Y n t)
        (coherentHomComparisonObj_cast X Y i) (coherentHomComparisonObj_last X Y n)
      erw [coherentHomComparisonHom_cast_last,
        coherentCompositionHom_zero_last (C := ClosedCategory A D)
        (X := X) (Y := Y) (Z := Y) σ (standardUnit (R := A) (D := D) y n) t i hi]
      erw [dgStandardUnit_yoneda A D y n]
      simp only [← Category.assoc, comp_toUnit]
      erw [dgStandardUnit_lift_comp_right A D]
      erw [dgCompositionUnitCollapseHom t hi _ (dgCompositionUnitCollapse_last t),
        dgCompositionUnitCollapseHom_maximum]
    · apply dgCoherentRightUnit_normalized A D σ t _ _ _ _ Y Y
        (dgCompositionUnitCollapse_one t i hi) (dgCompositionUnitCollapse_last t)
        (coherentCompositionObj_one X Y Y t i hi) (coherentCompositionObj_last X Y Y n t)
        (coherentHomComparisonObj_last X Y n) (coherentHomComparisonObj_last X Y n)
      erw [coherentHomComparisonHom_last_last,
        coherentCompositionHom_one_last (C := ClosedCategory A D)
        (X := X) (Y := Y) (Z := Y) σ (standardUnit (R := A) (D := D) y n) t i hi]
      erw [dgStandardUnit_yoneda A D y n]
      simp only [← Category.assoc, comp_toUnit]
      rfl
  case cast.cast i j =>
    by_cases hi : t i = 0 <;> by_cases hj : t j = 0
    · apply dgCoherentRightUnit_normalized A D σ t _ _ _ _ X X
        (dgCompositionUnitCollapse_zero t i hi) (dgCompositionUnitCollapse_zero t j hj)
        (coherentCompositionObj_zero X Y Y t i hi) (coherentCompositionObj_zero X Y Y t j hj)
        (coherentHomComparisonObj_cast X Y i) (coherentHomComparisonObj_cast X Y j)
      erw [coherentCompositionHom_zero_zero (C := ClosedCategory A D)
        (X := X) (Y := Y) (Z := Y) σ (standardUnit (R := A) (D := D) y n) t i j hi hj]
      erw [dgCoherentHomComparisonHom_cast_cast A D σ i j]
      simp only [← Category.assoc, comp_toUnit]
      rfl
    · apply dgCoherentRightUnit_normalized A D σ t _ _ _ _ X Y
        (dgCompositionUnitCollapse_zero t i hi) (dgCompositionUnitCollapse_one t j hj)
        (coherentCompositionObj_zero X Y Y t i hi) (coherentCompositionObj_one X Y Y t j hj)
        (coherentHomComparisonObj_cast X Y i) (coherentHomComparisonObj_last X Y n)
      erw [coherentHomComparisonHom_cast_last,
        coherentCompositionHom_zero_one (C := ClosedCategory A D)
        (X := X) (Y := Y) (Z := Y) σ (standardUnit (R := A) (D := D) y n) t i j hi hj]
      erw [← Category.assoc,
        dgCompositionUnitCollapseHom t hi _ (dgCompositionUnitCollapse_one t j hj)]
      erw [← Category.assoc, dgCompositionUnitCollapseHom_maximum]
    · apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro P
      exact (pathCut_backward_false t hi hj (P.obj 0)).elim
    · apply dgCoherentRightUnit_normalized A D σ t _ _ _ _ Y Y
        (dgCompositionUnitCollapse_one t i hi) (dgCompositionUnitCollapse_one t j hj)
        (coherentCompositionObj_one X Y Y t i hi) (coherentCompositionObj_one X Y Y t j hj)
        (coherentHomComparisonObj_last X Y n) (coherentHomComparisonObj_last X Y n)
      erw [coherentHomComparisonHom_last_last,
        coherentCompositionHom_one_one (C := ClosedCategory A D)
        (X := X) (Y := Y) (Z := Y) σ (standardUnit (R := A) (D := D) y n) t i j hi hj]
      simp only [← Category.assoc, comp_toUnit]
      rfl
/-- 同じ全図式の退化を、coherent nerve の実単体写像として表示する。 -/
lemma dgCoherentCompositionSimplex_second_unit_eq_map {x y : D} {n : ℕ}
    (σ : StandardSimplex A x y n) (t : Fin (n + 1) →o Fin 2) :
    coherentCompositionSimplex (C := ClosedCategory A D)
      (X := ForgetEnrichment.of (Complex A) x) (Y := ForgetEnrichment.of (Complex A) y)
      (Z := ForgetEnrichment.of (Complex A) y)
      σ (standardUnit (R := A) (D := D) y n) t =
      (SimplicialNerve (ClosedCategory A D)).map
        (SimplexCategory.mkHom (dgCompositionUnitCollapse t)).op
        (coherentHomComparisonSimplex (C := ClosedCategory A D)
          (X := ForgetEnrichment.of (Complex A) x) (Y := ForgetEnrichment.of (Complex A) y) σ) :=
  (dgCoherentCompositionSimplex_second_unit A D σ t).symm

end SerrePositivity.InfinityCategories
