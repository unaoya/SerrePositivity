module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FibrantModels.DGCoherentCompositionUnitLaws
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGComposition.DGCompositionUnitCollapse
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded
open SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

lemma dgCoherentCompositionObj_second_unit (x y : _root_.SerrePositivity.DifferentialGraded.ClosedCategory A D) {n : ℕ}
    (t : Fin (n + 1) →o Fin 2) (i : Fin (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj x y (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse t i) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj x y y t i := by
  induction i using Fin.lastCases with
  | last => simp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse_last, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_last]
  | cast i =>
    by_cases hi : t i = 0
    · simp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse_zero t i hi, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast,
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_zero x y y t i hi]
    · simp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse_one t i hi, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last,
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_one x y y t i hi]

lemma dgStandardUnit_lift_comp_right {x y : D} {K : SSet.{u}}
    (h : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := A) (D := D) x y) :
    lift h (toUnit K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnitMap (R := A) (D := D) y) ≫
      eComp SSet (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) = h := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_comp_id_app (ForgetEnrichment.of (Complex A) x)
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) _ (h.app _ a)

lemma dgCoherentHomComparisonHom_cast_cast {x y : D} {n : ℕ}
    (σ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex A x y n) (i j : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonHom (C := ClosedCategory A D)
      (X := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) (Y := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y)
      σ i.castSucc j.castSucc ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast (ForgetEnrichment.of (Complex A) x)
          (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) i)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast (ForgetEnrichment.of (Complex A) x)
          (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) j)) =
      toUnit _ ≫ eId SSet (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) := by
  simp -implicitDefEqProofs +instances [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonHom, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj]

lemma dgCoherentRightUnit_normalized {x y : D} {n : ℕ}
    (σ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex A x y n) (t : Fin (n + 1) →o Fin 2)
    (i j i' j' : Fin (n + 2)) (a b : _root_.SerrePositivity.DifferentialGraded.ClosedCategory A D)
    (hi : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse t i = i')
    (hj : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse t j = j')
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj (ForgetEnrichment.of (Complex A) x)
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) t i = a)
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj (ForgetEnrichment.of (Complex A) x)
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) t j = b)
    (ha' : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj (ForgetEnrichment.of (Complex A) x)
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) i' = a)
    (hb' : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj (ForgetEnrichment.of (Complex A) x)
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) j' = b)
    (h : (SimplicialThickening.functor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse t).uliftMap).map
        (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up j⟩ ≫
      eqToHom (congrArg₂ (fun a b : Fin (n + 2) => SimplicialCategory.sHom
        (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up b⟩) hi hj) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonHom (C := ClosedCategory A D)
        (X := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) (Y := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) σ i' j' ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom ha' hb') =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom (C := ClosedCategory A D)
        (X := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) (Y := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y)
        (Z := ForgetEnrichment.of (Complex A) y) σ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit (R := A) (D := D) y n) t i j ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom ha hb)) :
    ((SimplicialThickening.functor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse t).uliftMap).map
      (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up j⟩ ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonHom (C := ClosedCategory A D)
        (X := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) (Y := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y)
        σ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse t i) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse t j)) ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (dgCoherentCompositionObj_second_unit A D _ _ t i)
        (dgCoherentCompositionObj_second_unit A D _ _ t j)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom (C := ClosedCategory A D)
        (X := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) (Y := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y)
        (Z := ForgetEnrichment.of (Complex A) y) σ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit (R := A) (D := D) y n) t i j := by
  apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom ha hb))).1
  simp only [Category.assoc, eqToHom_trans]
  change _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonHom (C := ClosedCategory A D)
      (X := ForgetEnrichment.of (Complex A) x) (Y := ForgetEnrichment.of (Complex A) y)
      σ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse t i) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse t j) ≫
    eqToHom (congrArg₂ SimplicialCategory.sHom
      ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj (ForgetEnrichment.of (Complex A) x)
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y)) hi).trans ha')
      ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj (ForgetEnrichment.of (Complex A) x)
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y)) hj).trans hb')) = _
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_transport (C := ClosedCategory A D)
    (X := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) (Y := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y)
    σ hi hj ha' hb' ]
  simpa only [Category.assoc] using h

set_option maxHeartbeats 1200000 in
-- 全頂点対の分岐と端点輸送を一つの豊穣関手の等式へ束ねるため。
lemma dgCoherentCompositionSimplex_second_unit {x y : D} {n : ℕ}
    (σ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex A x y n) (t : Fin (n + 1) →o Fin 2) :
    (SimplicialThickening.functor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse t).uliftMap).comp SSet
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex (C := ClosedCategory A D)
        (X := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) (Y := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) σ) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionSimplex (C := ClosedCategory A D)
      (X := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) (Y := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y)
      (Z := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y)
      σ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit (R := A) (D := D) y n) t := by
  let X := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x
  let Y := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y
  apply EnrichedFunctor.ext SSet
    (fun i => dgCoherentCompositionObj_second_unit A D X Y t i.as.down)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  change (_ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonHom (C := ClosedCategory A D) (X := X) (Y := Y)
    σ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse t i)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse t j)) ≫ eqToHom _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom (C := ClosedCategory A D) (X := X) (Y := Y) (Z := Y)
        σ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit (R := A) (D := D) y n) t i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases
  case last.last =>
    apply dgCoherentRightUnit_normalized A D σ t _ _ _ _ Y Y
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse_last t) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse_last t)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_last X Y Y n t) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_last X Y Y n t)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last X Y n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last X Y n)
    erw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_last_last,
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_last_last]
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
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse_zero t i hi) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse_last t)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_zero X Y Y t i hi) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_last X Y Y n t)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast X Y i) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last X Y n)
      erw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_cast_last,
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_zero_last (C := ClosedCategory A D)
        (X := X) (Y := Y) (Z := Y) σ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit (R := A) (D := D) y n) t i hi]
      erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStandardUnit_yoneda A D y n]
      simp only [← Category.assoc, comp_toUnit]
      erw [dgStandardUnit_lift_comp_right A D]
      erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapseHom t hi _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse_last t),
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapseHom_maximum]
    · apply dgCoherentRightUnit_normalized A D σ t _ _ _ _ Y Y
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse_one t i hi) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse_last t)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_one X Y Y t i hi) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_last X Y Y n t)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last X Y n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last X Y n)
      erw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_last_last,
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_one_last (C := ClosedCategory A D)
        (X := X) (Y := Y) (Z := Y) σ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit (R := A) (D := D) y n) t i hi]
      erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStandardUnit_yoneda A D y n]
      simp only [← Category.assoc, comp_toUnit]
      rfl
  case cast.cast i j =>
    by_cases hi : t i = 0 <;> by_cases hj : t j = 0
    · apply dgCoherentRightUnit_normalized A D σ t _ _ _ _ X X
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse_zero t i hi) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse_zero t j hj)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_zero X Y Y t i hi) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_zero X Y Y t j hj)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast X Y i) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast X Y j)
      erw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_zero_zero (C := ClosedCategory A D)
        (X := X) (Y := Y) (Z := Y) σ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit (R := A) (D := D) y n) t i j hi hj]
      erw [dgCoherentHomComparisonHom_cast_cast A D σ i j]
      simp only [← Category.assoc, comp_toUnit]
      rfl
    · apply dgCoherentRightUnit_normalized A D σ t _ _ _ _ X Y
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse_zero t i hi) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse_one t j hj)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_zero X Y Y t i hi) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_one X Y Y t j hj)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast X Y i) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last X Y n)
      erw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_cast_last,
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_zero_one (C := ClosedCategory A D)
        (X := X) (Y := Y) (Z := Y) σ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit (R := A) (D := D) y n) t i j hi hj]
      erw [← Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapseHom t hi _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse_one t j hj)]
      erw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapseHom_maximum]
    · apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro P
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCut_backward_false t hi hj (P.obj 0)).elim
    · apply dgCoherentRightUnit_normalized A D σ t _ _ _ _ Y Y
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse_one t i hi) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse_one t j hj)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_one X Y Y t i hi) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_one X Y Y t j hj)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last X Y n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last X Y n)
      erw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_last_last,
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_one_one (C := ClosedCategory A D)
        (X := X) (Y := Y) (Z := Y) σ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit (R := A) (D := D) y n) t i j hi hj]
      simp only [← Category.assoc, comp_toUnit]
      rfl
/-- 同じ全図式の退化を、coherent nerve の実単体写像として表示する。 -/
lemma dgCoherentCompositionSimplex_second_unit_eq_map {x y : D} {n : ℕ}
    (σ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex A x y n) (t : Fin (n + 1) →o Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionSimplex (C := ClosedCategory A D)
      (X := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) (Y := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y)
      (Z := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y)
      σ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit (R := A) (D := D) y n) t =
      (SimplicialNerve (_root_.SerrePositivity.DifferentialGraded.ClosedCategory A D)).map
        (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse t)).op
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex (C := ClosedCategory A D)
          (X := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) (Y := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) σ) :=
  (dgCoherentCompositionSimplex_second_unit A D σ t).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
